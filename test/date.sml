open DateUtil

val ppDate = DateUtil.ppDate

(*
val fullDate = Date.toString
*)

fun dtest (s,d1,d2f) = Utest.testPP ppDate s d1 d2f

(*
fun dtestfull (s,d1,d2) = Utest.testPP fullDate s d1 (fn () => d2)
*)

(* Known bug: ignore week days or make sure you always pick Monday! ;-) *)
val today = ?"2013-01-01"

val tests1 = [ ("add nothing", (?"2013-01-01"), (fn () => addDays 0 today))
             , ("add one day", (?"2013-01-02"), (fn () => addDays 1 today))
             , ("add one (non-leap) year", (?"2014-01-01"), 
                (fn () => addDays 365 today))
             , ("add January", (?"2013-02-01"), (fn () => addDays 31 today))
             , ("add first 6 months of the year", 
                (?"2013-07-01"), (fn () => addDays (31+28+31+30+31+30) today))
             ]

fun testDiff i = Utest.testPP Int.toString
                              ("dateDiff test with difference " ^
                               (Int.toString i))
                              i (fn () => dateDiff today (addDays i today))
fun testDiff2 dt i = dt ("dateDiff back and forth",
                         today, fn () => addDays (~i) (addDays i today))
                         
val () = app testDiff (List.tabulate ( 36, fn i => 10*i-31 ))
val () = app (testDiff2 dtest) (List.tabulate ( 10, fn i => 25+10*i ))

val () = app dtest tests1

(*
val () = app dtestfull tests1
*)

