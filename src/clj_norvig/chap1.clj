(ns clj-norvig.chap1
  (:require [clojure.string :as s]))


;; Exercise 1.1
(def honorifics #{"jr" "md" "ii" "iii" "phd" "esq"})

(def punctuation #"[\.,!\?\*]")

(defn clean-lower [token]
  (-> token
      (s/lower-case)
      (s/replace punctuation "")))

(defn clean [token]
  (s/replace token punctuation ""))

(defn last-name [full-name]
  (let [split-full-name (s/split full-name #"\s+")
        lname (last split-full-name)]
    (if (not (honorifics (clean-lower lname)))
      (clean lname)
      (recur (apply str (interpose " " (butlast split-full-name)))))))

;; Exercise 1.2

(defn power [base exp]
  {:pre [(>= exp 0)]}
  (if (= exp 0) 1
      (* base  (power base (dec exp)))))


;; Exercise 1.3

(defn count-atoms [exp]
  (cond (string? exp) 1
        (not (sequential? exp)) 1
        (empty? exp) 0
        true (+ (count-atoms (first exp)) (count-atoms (rest exp)))))


;; Exercise 1.4

(defn count-anywhere [target exp]
  (cond (= target exp) 1
        (not (sequential? exp)) 0
        (empty? exp) 0
        true (+ (count-anywhere target (first exp))
                (count-anywhere target (rest exp)))))

;; Exercise 1.5

(defn dot-product [seq1 seq2]
  {:pre [(= (count seq1) (count seq2))]}
  (reduce +  (map * seq1 seq2)))
