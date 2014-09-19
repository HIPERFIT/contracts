structure DateUtil :> DateUtil = struct 

type date = Date.date
exception DateError of string

(* module functions operate on the Date.date type, ignoring time *)

(* The expected format of our converter is yyyy-mm-dd. Suffix is ignored *)
fun ? s = let val y  = String.substring (s,0,4) 
              val m  = case String.substring(s,5,2) of
                           "01" => "Jan "
                         | "02" => "Feb "
                         | "03" => "Mar "
                         | "04" => "Apr "
                         | "05" => "May "
                         | "06" => "Jun "
                         | "07" => "Jul "
                         | "08" => "Aug "
                         | "09" => "Sep "
                         | "10" => "Oct "
                         | "11" => "Nov "
                         | "12" => "Dec "
                         | other => raise DateError "garbled date"
              val d  = String.substring (s,8,2)
              val bogus = case Date.fromString  ("Mon " ^ m ^ d ^ " 00:00:00 " ^ y) of
                              SOME x => x
                            | NONE => raise DateError ("date conversion failed for " ^
                                                   "Mon " ^ m ^ d ^ " 00:00:00 " ^ y)
          in (* correcting the weekday: *)
              Date.fromTimeLocal (Date.toTime bogus)
          end

fun addDays i d =
    let val t = Date.toTime d (* uses local time! see below *)
        val seconds = real i * 24.0*60.0*60.0
        (* Mosml's Time.fromSeconds function has a wrong type, thus it is 
         * necessary to use the real representation for portability *)
        val off = Time.fromReal seconds
        val t' = Time.+(t,off)
    in Date.fromTimeLocal t' (* local time is used...
                                TODO problem with daylight saving *)
    end

(* computes day difference to go from d1 to d2 *)
fun dateDiff d1 d2 =
    let val t1 = Date.toTime d1
        val t2 = Date.toTime d2
        val t = Time.-(t2,t1)
        val s = Time.toSeconds t
    in LargeInt.toInt(((s div 24) div 60) div 60)
    end

val ppDate = Date.fmt "%Y-%m-%d"
val compare = Date.compare
end

