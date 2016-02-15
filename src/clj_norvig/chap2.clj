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
