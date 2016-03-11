(ns clj-norvig.chap2
  (:require [clojure.string :as s]))

;; Exercise 2.1 -- generate w/ cond

(def simple-grammar
  '((sentence  -> (noun-phrase verb-phrase))
    (noun-phrase -> (Article Noun))
    (verb-phrase -> (Verb noun-phrase))
    (Article -> the a)
    (Noun -> man ball woman table)
    (Verb -> hit took saw liked)))


(def ^:dynamic *grammar* simple-grammar)

(defn rule [rule-sym]
  (first (filter #(= rule-sym (first %)) *grammar*)))

(defn rule-lhs [rule-sym]
  (first (rule rule-sym)))

(defn rule-rhs [rule-sym]
  (rest (rest (rule rule-sym))))

(defn rewrites [category]
  (let[rw (rule-rhs category)]
    (when (not (empty? rw)) rw)))

(defn generate [phrase]
  (cond
    (sequential? phrase) (mapcat generate phrase)
    (rewrites phrase) (generate (rand-nth (rewrites phrase)))
    true (list phrase)))

;; Exercise 2.2 -- generate w/ explicit


(defn terminal? [phrase]
  (nil? (rewrites phrase)))

(defn egenerate [phrase]
  (cond
    (sequential? phrase) (mapcat egenerate phrase)
    (not (terminal? phrase)) (egenerate (rand-nth (erewrites phrase)))
    true (list phrase)))


;; From 2.5 -- bigger grammar
(def bigger-grammar
  '((sentence -> (noun-phrase verb-phrase))
    (noun-phrase -> (Article Adj* Noun PP*) (Name) (Pronoun))
    (verb-phrase -> (Verb noun-phrase PP*))
    (PP* -> () (PP PP*))
    (Adj* -> () (Adj Adj*))
    (PP -> (Prep noun-phrase))
    (Prep -> to in by with on)
    (Adj -> big little blue green adiabatic)
    (Article -> the a)
    (Name -> Pat Kim Lee Terry Robin)
    (Noun -> man ball woman table)
    (Verb -> hit took saw liked)
    (Pronoun -> he she it these those that)))

(defn set-grammar! [kw]
  (when (kw grammars)
    (alter-var-root #'*grammar* (constantly (kw grammars)))))


;; Section 2.6 -- Generate Tree Example

(defn generate-tree [phrase]
  (cond
    (sequential? phrase) (map generate-tree phrase)
    (rewrites phrase) (cons phrase (generate-tree (rand-nth (rewrites phrase))))
    true (list phrase)))

;; Exercise 2.3

(def sql-subset-grammar
  '((statement -> (Action Value From Table))
    (Action -> select insert delete)
    (Value -> * id)
    (From -> from)
    (Table -> users companies)))

(def grammars {:simple simple-grammar
               :bigger bigger-grammar
               :sql sql-subset-grammar})

;; Exercise 2.4

(defn cross-product [f xlist ylist]
  (mapcat (fn [y] (map (fn [x] (f x y)) xlist)) ylist))

(defn combine-all [xlist ylist]
  (cross-product concat xlist ylist))


;; Generate All -- section 2.6
(declare generate-all)

(defn handle-sequential [phrase]
  (combine-all (generate-all (first phrase))
               (generate-all (rest phrase))))

(defn generate-all [phrase]
  (cond
    (or (nil? phrase)
        (and (sequential? phrase) (empty? phrase))) (list nil)
    (sequential? phrase) (handle-sequential phrase)
    (rewrites phrase) (mapcat generate-all (rewrites phrase))
    true (list (list phrase))))
