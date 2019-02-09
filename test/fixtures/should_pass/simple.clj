(ns fixtures.should-pass.simple)

(defn foo [x] (inc x))

(defn bar [x] (foo x))
