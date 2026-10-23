-- expect: #eval
#eval IO.println "runs during elaboration"
theorem holds : True := trivial
