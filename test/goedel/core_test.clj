(ns goedel.core-test
  (:require [goedel.core :as sut]
            [clojure.test :refer :all]
            [clojure.java.io :as io]))

(defn- fixture-files [dir]
  (->> (io/file (System/getProperty "user.dir") "test" "fixtures" dir)
       file-seq
       (filter #(.isFile %))))

(deftest check-file-test
  (testing "should pass"
    (doseq [f (fixture-files "should_pass")]
      (is (sut/check-file f)))))
