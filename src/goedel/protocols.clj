(ns goedel.protocols)


(defprotocol AsJavaClass
  :extend-via-metadata true
  (as-java-class [x]))

(extend-protocol AsJavaClass
  Class
  (as-java-class [x] x))


(defprotocol Type
  :extend-via-metadata true
  (parents [this])
  (children [this]))
