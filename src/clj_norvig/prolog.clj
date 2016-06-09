(ns clj-norvig.prolog
  (:require [clojure.set :as set]))

(def fail nil)

(def no-bindings {true true})

(defn variable? [x]
  (when (symbol? x)
    (= \? (first (name x)))))

(defn lookup
  [var bindings]
  (get bindings var))

(defn extend-bindings
  [var val bindings]
  (if (= bindings no-bindings)
    (assoc {} var val)
    (assoc bindings var val)))

(defn match-variable
  [var input bindings]
  (let [binding (lookup var bindings)]
    (cond (not binding) (extend-bindings var input bindings)
          (= input binding) bindings
          true fail)))

(declare unify-variable)
(declare t-unify-variable)
(declare occurs-check)

(defn unify
  ([x y bindings]
   (cond
     (= bindings fail) fail
     (= x y) bindings
     (variable? x) (unify-variable x y bindings)
     (variable? y) (unify-variable y x bindings)
     (and (seq? x) (seq? y)) (recur (rest x) (rest y)
                                  (unify (first x) (first y) bindings))
     :else fail))
  ([x y]
   (unify x y no-bindings)))

(defn unify-variable
  [var x bindings]
  (cond
    (lookup var bindings) (unify (lookup var bindings) x bindings)
    (and (variable? x)
         (lookup x bindings)) (unify var (lookup x bindings) bindings)
         :else (extend-bindings var x bindings)))

(defn t-unify
  ([x y bindings]
   (cond
     (= bindings fail) fail
     (= x y) bindings
     (variable? x) (t-unify-variable x y bindings)
     (variable? y) (t-unify-variable y x bindings)
     (and (seq? x) (seq? y)) (recur (rest x) (rest y)
                                  (t-unify (first x) (first y) bindings))
     :else fail))
  ([x y]
   (t-unify x y no-bindings)))

(defn t-unify-variable
  [var x bindings]
  (cond
    (lookup var bindings) (unify (lookup var bindings) x bindings)
    (and (variable? x)
         (lookup x bindings)) (unify var (lookup x bindings) bindings)
         (occurs-check var x bindings)
         (throw (ex-info "Infinite Unification Detected!"
                         {:causes #{:infinite-unification}
                          :var var :x x :bindings bindings}))
         :else (extend-bindings var x bindings)))

(defn occurs-check
  [var x bindings]
  (cond
    (= var x) true
    (and (variable? x) (lookup x bindings))
    (occurs-check var (lookup x bindings) bindings)
    (seq? x) (or (occurs-check var (first x) bindings)
                (occurs-check var (rest x) bindings))
    :else nil))

(defn reuse-cons
  [x y x-y]
  (if (and (= x (first x-y) (= y (rest x-y))))
    x-y
    (cons x y)))

(defn atomic?
  [x]
  (or (and x (not (seq? x)))
      (and (seq? x) (empty? x))))

(defn subst-bindings
  [bindings x]
  (cond (= bindings fail) fail
        (= bindings no-bindings) x
        (and (variable? x) (lookup x bindings))
        (subst-bindings bindings (lookup x bindings))
        (atomic? x) x
        :else (reuse-cons (subst-bindings bindings (first x))
                          (subst-bindings bindings (rest x))
                          x)))

(defn unifier
  [x y]
  (subst-bindings (unify x y) x))

(defn t-unifier
  [x y]
  (subst-bindings (t-unify x y) x))


;; Prolog-in-Clj

(defonce db (atom {}))

(defn clear-db
  []
  (swap! db (constantly {})))

(defn clear-predicate
  [predicate]
  (swap! db (fn [old] (dissoc old predicate))))


(defn clause-head
  [clause]
  (first clause))

(defn clause-body
  [clause]
  (rest clause))

(defn get-clauses
  [pred]
  (get @db pred))

(defn predicate
  [relation]
  (first relation))

(defn add-clause
  [clause]
  (let [pred (predicate (clause-head clause))]
    (assert (and (symbol? pred) (not (variable? pred))))
    (swap! db (fn [old] (update old pred concat (list clause))))))

(defn <-
  [& clause]
  (add-clause clause))

(defn unique-find-anywhere-if
  ([predicate tree found-so-far]
   (if (atomic? tree)
     (if (predicate tree)
       (conj found-so-far tree)
       found-so-far)
     (recur predicate (first tree)
            (unique-find-anywhere-if predicate (rest tree) found-so-far))))
  ([predicate tree]
   (unique-find-anywhere-if predicate tree #{})))

(defn variables-in
  [exp]
  (unique-find-anywhere-if variable? exp))

(defn rename-variables
  [x]
  (let [variables (variables-in x)
        replace-with (into {} (map (fn [x] {x (gensym x)}) variables))
        walk-fn (fn [var]
                  (if-let [new-var (get replace-with var)]
                    new-var
                    var))]
    (clojure.walk/postwalk walk-fn x)))


(declare prove-all)

(defn prove
  [goal bindings]
  (let [clauses (get-clauses (predicate goal))]
    (mapcat (fn [clause]
              (let [new-clause (rename-variables clause)]
                (prove-all (clause-body new-clause)
                           (t-unify goal (clause-head new-clause) bindings))))
            clauses)))


(defn prove-all
  [goals bindings]
  (cond
    (= bindings fail) fail
    (empty? goals) (list bindings)
    :else
    (mapcat (fn [goal-solution]
              (prove-all (rest goals) goal-solution))
            (prove (first goals) bindings))))

(defn show-prolog-vars
  [vars bindings]
  (if (empty? vars) (println "Yes.")
      (doseq [var vars]
        (println (format " %s = %s;" var (subst-bindings bindings var))))))


(defn show-prolog-solutions
  [vars solutions]
  (if (empty? solutions)
    (println  "No.")
    (doseq [solution solutions]
      (show-prolog-vars vars solution))))

(defn top-level-prove
  [goals]
  (show-prolog-solutions
   (variables-in goals)
   (prove-all goals no-bindings)))


(defn ?- [& goals]
  (top-level-prove goals))

(defn load-db
  "load fresh DB to test"
  []
  (clear-db)
  (<- '(likes kim robin))
  (<- '(likes sandy lee))
  (<- '(likes sandy kim))
  (<- '(likes robin cats))
  (<- '(likes sandy ?x) '(likes ?x cats))
  (<- '(likes kim ?x) '(likes ?x lee) '(likes ?x kim))
  (<- '(likes ?x ?x)))
