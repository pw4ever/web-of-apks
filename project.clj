(defproject woa "0.1.0-SNAPSHOT"
  :description ""
  :url "https://github.com/pw4ever/woa"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  :dependencies [[org.clojure/clojure "1.6.0"]
                 [org.clojure/tools.cli "0.3.1"]
                 [org.clojure/tools.nrepl "0.2.5"]
                 [org.clojure/data.json "0.2.5"]
                 [org.clojure/core.async "0.1.346.0-17112a-alpha"]

                 ;; the workhorses
                 [asmdex/asmdex "1.0"]
                 [soot/soot "1.0"]

                 ;; utilties
                 ;;[clj-http "1.0.1"]
                 [pandect "0.4.1"]
                 [commons-io/commons-io "2.4"]
                 [incanter/incanter-core "1.5.6"]
                 [me.raynes/fs "1.4.6"]
                 [com.taoensso/nippy "2.7.1"]
                 [clojurewerkz/neocons "3.0.0"]]
  :plugins [[lein-localrepo "0.5.3"]
            [cider/cider-nrepl "0.8.1"]
            [lein-marginalia "0.8.0"]]
  :repositories {"sonatype-oss-public" "https://oss.sonatype.org/content/groups/public/"}
  :main ^:skip-aot woa.core
  :target-path "target/%s"
  :uberjar-name "woa.jar"
  :jvm-opts ["-Xmx2048M"]
  :profiles {:uberjar {:aot :all}})
