(ns clj-norvig.prolog)

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
