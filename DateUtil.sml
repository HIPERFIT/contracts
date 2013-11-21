structure DateUtil  = struct 
(* ************* a custom Date module ***************** *)

exception Error of string

(* module functions operate on the Date.date type, ignoring time *)

(* The expected format of our converter is yyyy-mm-dd. Suffix is ignored *)
fun ? s = let val y  = String.substring (s,0,4) 
              val m  = case String.substring(s,5,2) of
                           "01" => " Jan "
                         | "02" => " Feb "
                         | "03" => " Mar "
                         | "04" => " Apr "
                         | "05" => " May "
                         | "06" => " Jun "
                         | "07" => " Jul "
                         | "08" => " Aug "
                         | "09" => " Sep "
                         | "10" => " Oct "
                         | "11" => " Nov "
                         | "12" => " Dec "
                         | other => raise Error "garbled date"
              val d  = String.substring (s,8,2)
          in case Date.fromString  ("Mon " ^ m ^ d ^ " 00:00:00 " ^ y) of
                 SOME x => x
               | NONE => raise Error "date conversion failed"
          end

(* computing with dates -- an internal representation as
   days-since-epoch would pay off quickly... 
*)
(* detect leap years *)
fun daysInY year = if year mod 4 = 0 andalso not (year mod 100 = 0)
                  then 366 else 365
(* daysInM*)
fun daysInM Date.Feb yy = if yy mod 4 = 0 andalso not (yy mod 100 = 0)
                          then 29 else 28
  | daysInM Date.Apr _ = 30
  | daysInM Date.Jun _ = 30
  | daysInM Date.Sep _ = 30
  | daysInM Date.Nov _ = 30
  | daysInM other    _ = 31

(* next month *)
fun next Date.Jan = Date.Feb
  | next Date.Feb = Date.Mar
  | next Date.Mar = Date.Apr
  | next Date.Apr = Date.May
  | next Date.May = Date.Jun
  | next Date.Jun = Date.Jul
  | next Date.Jul = Date.Aug
  | next Date.Aug = Date.Sep
  | next Date.Sep = Date.Oct
  | next Date.Oct = Date.Nov
  | next Date.Nov = Date.Dec
  | next Date.Dec = raise Error "next Dec"

(* yearDay to month/day *)
fun yearDayToMD yd yy =
    let fun yearMD month yd = let val dm = daysInM month yy
                              in if yd <= dm then (month,yd) 
                                 else yearMD (next month) (yd-dm)
                              end
    in yearMD Date.Jan (yd+1) (* yearDay starts from 0! *) 
    end

(* *)
fun addDays days date = 
    if days < 0 then raise Error "addDays: negative"
    (* else if days = 0 then date *)
    else let val yd = Date.yearDay date 
             val yy = Date.year date 
             val mm = Date.month date
             val dd = Date.day date
         in if yd + days >= daysInY yy (* NB ">=", yearDay starts from 0 *)
            then addDays (* advance to 1st of January *)
                     (days - (daysInY yy - yd))
                     (Date.date { year = yy+1, month = Date.Jan, day=1,
                                  hour = 0, minute = 0, second = 0,
                                  offset = NONE })
            else let val (m, d) = yearDayToMD (yd + days) yy
                 in Date.date {year = yy, month = m, day = d, hour = 0, 
                               minute = 0, second = 0, offset = NONE}
                 end
         end

(* computes day difference to go from d1 to d2 *)
fun dateDiff d1 d2 = if Date.compare (d1,d2) = GREATER
                     then 0 - dateDiff d2 d1
                     else (* when here: year difference is positive *)
                         let val (yd1,yd2) = (Date.year d1, Date.year d2)
                             val yDiff = List.foldl (op +) 0 
                                         (List.tabulate 
                                              ((yd2 - yd1)
                                               ,(fn i => daysInY (i+yd1))))
                             val dDiff = Date.yearDay d2 - Date.yearDay d1
                         in yDiff + dDiff 
                         end

val ppDate = Date.fmt "%Y-%m-%d"

(* ************************************************ *)

end

