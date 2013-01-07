;;Syntax notes:
;;^Type is a type hint for java interop. It indicated the following identifier should be the indicated type. [^String file] indicates that file should be a string.

;;TODO make 59 not hardcoded everywhere.


(ns tacaa.parser
  (:import (java.io InputStream FileInputStream)
           (se.sics.isl.transport Transportable)
           (se.sics.tasim.logtool LogReader ParticipantInfo)
           (edu.umich.eecs.tac Parser TACAAConstants)
           (edu.umich.eecs.tac.props BankStatus SlotInfo ReserveInfo PublisherInfo
                                     SalesReport QueryReport BidBundle RetailCatalog
                                     UserClickModel AdvertiserInfo UserPopulationState
                                     Ad Product Query QueryType)))

(def file "/Users/jordanberg/Documents/workspace/Clients/game1.slg")

(def messages (atom []))

(def day (atom -1))

(defn mk-game-parser
  "Input: A string indicating a filename and a reader for that file. If the reader is not provided a default LogReader is created.
  Output: A Parser object for the given file with the ability to update the messages atom as indicated in the below functions."
  ([^String file] (mk-game-parser file (new LogReader (new FileInputStream file))))
  ([^String file reader]
      "Proxy is used to make a class with the Parser and reader class types implemented using the following definitions of abstract functions"
     (proxy [Parser] [reader]
       (message [from to content]
       "Adds to the messages atom the new message including the day the message we sent, the content, the sender, and the recipient.
       Inputs: String indicating the sender, recipient, and content.
       Output: The new value of message."
                (swap! messages conj [from to @day content]))
       (dataUpdated
       "When called with three arguments updates the messages vector, but not when called with two arguments."
        ([agent type value]
           (when (instance? UserPopulationState value)
             (swap! messages conj [agent type @day value])))
        ([type content] ()))
       (nextDay 
       "Sets day to be the indicated first argument. second argument seems ignored" 
       [date serverTime] (reset! day date)))))


(defn mk-queryspace
  "Returns a query space given a retail catalog. That is, for each item in the retailer's catelog, gets its manufactuer and component and find all possible queries that could match that item.
  In this way it returns a collection of queries that could match any item in the retailer's catalog."
  (reduce (fn [coll ^Product val] (let [man (.getManufacturer val)
                                       comp (.getComponent val)
                                       f1cq (new Query nil comp)
                                       f1mq (new Query man nil)
                                       f2q (new Query man comp)]
                                   (reduce conj coll [f1cq f1mq f2q]))) #{(new Query)} retail))

(defn remove-nan-bids
  "Input: The bidbundle currently being generated and the last bidbundle that was generated. As well as a list of possible queries.
    Output: If any queries, ads, or budgets are invalid, replaces them with the value that was used in the last bundle. Then returns the resulting bidbundle."
  ([^BidBundle bundle ^BidBundle lastbundle queryspace]
     (let [^BidBundle newbundle (reduce (fn [^BidBundle coll ^Query val]
                                          (do
                                            (if (not (.containsQuery bundle val))
                                              (.addQuery coll val 0 (new Ad) 0)
                                              (let [bid (.getBid bundle val)
                                                    newbid (if (or (Double/isNaN bid) (< bid 0))
                                                             (.getBid lastbundle val)
                                                             bid)
                                                    budget (.getDailyLimit bundle val)
                                                    newbudget (if (Double/isNaN budget)
                                                                (.getDailyLimit lastbundle val)
                                                                budget)
                                                    ad (.getAd bundle val)
                                                    newad (if (nil? ad)
                                                            (.getAd lastbundle val)
                                                            ad)]
                                                (.addQuery coll val newbid newad newbudget)))
                                            coll))
                                        (new BidBundle) queryspace)
           total-budget (.getCampaignDailySpendLimit bundle)]
       (do (if (Double/isNaN total-budget)
             (.setCampaignDailySpendLimit newbundle (.getCampaignDailySpendLimit lastbundle))
             (.setCampaignDailySpendLimit newbundle total-budget))
           newbundle)))
           ;;Overloaded version of the previous function where the defaults are instead 0.0 for all query budgets, ads displayed for each query that 
           ;;were not previously set are set to being general, and the overall budget if not properly set is set to the maximum possible.
  ([^BidBundle bundle queryspace]
     (let [^BidBundle newbundle (reduce (fn [^BidBundle coll ^Query val]
                                          (do
                                            (if (not (.containsQuery bundle val))
                                              (.addQuery coll val 0 (new Ad) 0)
                                              (let [bid (.getBid bundle val)
                                                    newbid (if (or (Double/isNaN bid) (< bid 0))
                                                             0.0
                                                             bid)
                                                    budget (.getDailyLimit bundle val)
                                                    newbudget (if (Double/isNaN budget)
                                                                Double/MAX_VALUE
                                                                budget)
                                                    ad (.getAd bundle val)
                                                    newad (if (nil? ad)
                                                            (new Ad)
                                                            ad)]
                                                (.addQuery coll val newbid newad newbudget)))
                                            coll))
                                        (new BidBundle) queryspace)
           total-budget (.getCampaignDailySpendLimit bundle)]
       (do (if (Double/isNaN total-budget)
             (.setCampaignDailySpendLimit newbundle Double/MAX_VALUE)
             (.setCampaignDailySpendLimit newbundle total-budget))
           newbundle))))

(defn mk-empty-bundle
  "When we make a new bundle in AA it sets the default total budget
   to be NaN, but we don't want any NaNs.  So create a new bundle and
   set a new total budget before returning"
  []
  (let [bundle (new BidBundle)]
    (do (.setCampaignDailySpendLimit bundle Double/MAX_VALUE)
        bundle)))

(defn check-bid-bundles
  "Input: status of a game
  Output: ensures that there are 59 bidbundles in the bidbundle collection part of the game status."
  [status]
  (let [bid-bundles (status :bid-bundle)]
    (assoc status :bid-bundle
           (reduce (fn [coll [agent val]]
                     (assoc coll agent
                            (let [bundles (bid-bundles agent)
                                  numbundles (count bundles)]
                                  ;;What does this do if numbundles > 59 or < 0. TODO
                              (if (== numbundles 59)
                                bundles
                                (reduce conj
                                        bundles ;replicate bundles as needed
                                        (vec (replicate (- 59 numbundles)
                                                        (peek bundles))))))))
                   {} bid-bundles))))

(defn parse-messages
  "Parses all of the messages into a game status"
  ([status messages]
     (if (seq messages) ;;if messages is non-empty.
       (recur
        (let [[from to day content] (first messages)
              from ((status :partic-names) from)
              to ((status :partic-names) to)]
          (cond
           (instance? BidBundle content) (if (< day 59) ;;the day of the current message
                                           (if (status :bid-bundle) ;;the bid-bundle exists in the status.
                                             (let [bid-bundle (status :bid-bundle)]
                                               (if (bid-bundle from)  ;;from exists in the bid-bundle                           
                                                 (let [bundles (bid-bundle from)
                                                       numbundles (count bundles)
                                                       lastbundle (peek bundles)
                                                       newbundle (remove-nan-bids content ;;newbundle of bids being added.
                                                                                  lastbundle
                                                                                  (status :query-space))]
                                                   (if (< day numbundles) ;too many bundles
                                                     (assoc status :bid-bundle
                                                            (assoc bid-bundle from
                                                                   (conj (pop bundles) newbundle))) ;remove one, then add the newbundle. TODO how do you know only 1 is enough to remove?
                                                     (assoc status :bid-bundle
                                                            (assoc bid-bundle from
                                                                   (reduce conj
                                                                           bundles ;replicate bundles as needed
                                                                           (conj (vec (replicate (- day numbundles)
                                                                                                 lastbundle)) ;extend the last bundle out to the day currently being added.
                                                                                 newbundle))))))
                                                 (let [newbundle (remove-nan-bids content (status :query-space))]
                                                   (assoc status :bid-bundle
                                                          (assoc bid-bundle from
                                                                 (reduce conj []
                                                                         (conj (vec (replicate day
                                                                                               (mk-empty-bundle))) ;;put empty bundles in all the days before this one. Then add the bidbundle.
                                                                                               ;;TODO remove duplicate code between this and the other if case... I'm sure there is some.
                                                                               newbundle)))))))
                                             (let [newbundle (remove-nan-bids content (status :query-space))] ;;bid-bundle does not exist in status.
                                               (assoc status :bid-bundle
                                                      {from (reduce conj []
                                                                  (conj (vec (replicate day
                                                                                        (mk-empty-bundle))) 
                                                                        newbundle))}))) ;;adds enough empty bundles to the status to account for previous days up til the newbundle's day.
                                                                        ;;Then adds the newbundle to the bid-bundle collection stored in the status.
                                           (let [bid-bundle (status :bid-bundle) ;;day is not < 59.
                                                 bundles (bid-bundle from)
                                                 numbundles (count bundles)
                                                 lastbundle (peek bundles)]
                                             (if (< numbundles 59)
                                               (assoc status :bid-bundle
                                                      (assoc bid-bundle from
                                                             (reduce conj
                                                                     bundles ;replicate bundles as needed
                                                                     (vec (replicate (- 59 numbundles) ;;replicate the last bid-bundle out to day 59. and ignore the content.
                                                                                     lastbundle))))) 
                                               status)))
           (instance? SalesReport content) (if (> day 1)
                                             (if (status :sales-report)
                                               (let [sales-report (status :sales-report)]
                                                 (if (sales-report to)
                                                   (assoc status :sales-report
                                                          (assoc sales-report to
                                                                 (conj (sales-report to) content))) ;;adds the content to the sales-report for to. initializes if necessary.
                                                   (assoc status :sales-report
                                                          (assoc sales-report to [content]))))
                                               (assoc status :sales-report {to [content]}))
                                             status)
           (instance? QueryReport content) (if (> day 1)
                                             (if (status :query-report)
                                               (let [query-report (status :query-report)]
                                                 (if (query-report to)
                                                   (assoc status :query-report
                                                          (assoc query-report to
                                                                 (conj (query-report to) content))) ;;adds the content to the query report. initializes collections if necessary.
                                                   (assoc status :query-report
                                                          (assoc query-report to [content]))))
                                               (assoc status :query-report {to [content]}))
                                             status)
           (instance? BankStatus content) (if (> day 0)
                                            (if (status :bank-stat)
                                              (let [bank-stat (status :bank-stat)]
                                                (if (bank-stat to)
                                                  (assoc status :bank-stat
                                                         (assoc bank-stat to
                                                                (conj (bank-stat to) content))) ;;adds the content to the bank status. initializes collections if necessary.
                                                  (assoc status :bank-stat
                                                         (assoc bank-stat to [content]))))
                                              (assoc status :bank-stat {to [content]}))
                                            status)
           (instance? UserPopulationState content) (if (> day 0)
                                                     (let [retail (seq (status :retail-cat)) ;;retail = new seq(status.get(:retail-cat))
                                                           contvec (reduce (fn [coll val]
                                                                             (assoc coll val
                                                                                    (seq (. ^UserPopulationState content (getDistribution ^Product val)))))
                                                                           {} (seq retail))] ;;associates each product in the catalog with its distribution in a map.
                                                       (if (status :user-pop) ;;if status already contains a UserPopulationState
                                                         (assoc status :user-pop
                                                                (conj (status :user-pop) contvec)) ;;add this state to the vector.
                                                         (assoc status :user-pop [contvec]))) ;;otherwise create the vector.
                                                     status) ;;return status if the day <= 0.
            ;;The following 4 only put their Info into the status if the status does not yet contain Info of the appropriate type.
           (instance? SlotInfo content) (if (status :slot-info) 
                                          status
                                          (assoc status :slot-info content))
           (instance? ReserveInfo content) (if (status :reserve-info)
                                             status
                                             (assoc status :reserve-info content))
           (instance? PublisherInfo content) (if (status :publish-info)
                                               status
                                               (assoc status :publish-info content))
           (instance? UserClickModel content) (if (status :user-click)
                                                status
                                                (assoc status :user-click content))
            ;;if the RetailCatalog is already in the status, don't change status, otherwise set the retail catalog and associated variable in the status.
           (instance? RetailCatalog content) (if (status :retail-cat)
                                               status
                                               (let [queryspace (mk-queryspace content)]
                                                 (merge status {:retail-cat content,
                                                                :query-space queryspace,
                                                                :qsf0 #{(new Query)},
                                                                :qsf1 (into #{} (filter (fn [^Query query] (= (.getType query)
                                                                                                             QueryType/FOCUS_LEVEL_ONE)) queryspace))
                                                                :qsf2 (into #{} (filter (fn [^Query query] (= (.getType query)
                                                                                                             QueryType/FOCUS_LEVEL_TWO)) queryspace))})))
           ;;Creates a map of advertiser info if it doesn't exist already, otherwise adds to an existing map. Uses the to field of the message to map to content.
           (instance? AdvertiserInfo content) (if (status :adv-info)
                                                (assoc status :adv-info
                                                       (assoc (status :adv-info) to
                                                              content))
                                                (assoc status :adv-info {to content}))
           :else status)) ;;doesn't modify status if the content is none of the above classes.
        (rest messages)) ;;recur on the rest of the messages.
       (check-bid-bundles status)))) ;;if messages is empty, check-bid-bundles before exiting.

(defn reset-parser
  []
  (do
    (reset! messages [])
    (reset! day -1)))

(defn parse-file
  [^String file]
  (do
    (reset-parser)
    (let [reader (new LogReader (new FileInputStream file))
          participants (seq (.getParticipants reader))
          partic-names (reduce (fn [coll ^ParticipantInfo val] (assoc coll
                                               (.getIndex val)
                                               (.getName val)))
                               {} participants)
          is-advertiser (reduce (fn [coll ^ParticipantInfo val] (assoc coll
                                               (.getIndex val)
                                               (= TACAAConstants/ADVERTISER (.getRole val))))
                                {} participants)
          agents (vec (filter identity
                              (map (fn [name is-adv]
                                     (if (peek is-adv)
                                       (peek name)
                                       nil)) partic-names is-advertiser)))
          ^Parser parser (mk-game-parser file reader)]
      (.start parser)
      (let []
        (parse-messages {:agents agents :partic-names partic-names} @messages)))))
