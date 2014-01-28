structure DateUtil :> DateUtil = struct 

type date = {year:int,month:int,day:int}

fun isLeapYear year =
    year mod 400 = 0 orelse
    (not (year mod 100 = 0) andalso year mod 4 = 0)
    
fun daysInYear year =
    if isLeapYear year then 366 else 365

fun daysInMonth year m =
    let val m31 = [1,3,5,7,8,10,12]
        fun daysInFeb () = if isLeapYear year then 29 else 28
    in if List.exists (fn x => x = m) m31 then 31
       else if m = 2 then daysInFeb()
       else 30
    end

fun check {year,month,day} =
    year >= 1 andalso year <= 9999 andalso  (* there is no such thing as year 0! *)
    month >= 1 andalso month <= 12 andalso
    day >= 1 andalso day <= daysInMonth year month 

exception DateError of string

(* module functions operate on the Date.date type, ignoring time *)

(* The expected format of our converter is yyyy-mm-dd. Suffix is ignored *)
fun dateError s =
    (print (s ^ "\n");
     raise DateError ("Expecting date in the form YYYY-MM-DD - got " ^ s))

fun digits s = CharVector.all Char.isDigit s

fun ? s =
    if size s <> 10 orelse String.sub(s,4) <> #"-" orelse String.sub(s,7) <> #"-" then dateError s
    else
      let val y = String.substring (s,0,4) 
          val m = String.substring (s,5,2)
          val d = String.substring (s,8,2)
      in if digits y andalso digits m andalso digits d then
           case (Int.fromString y, Int.fromString m, Int.fromString d) of
               (SOME y, SOME m, SOME d) => {year=y,month=m,day=d}
             | _ => dateError s
         else dateError s
      end

fun pad n s = if size s < n then pad n ("0" ^ s)
              else s

fun ppDate {year,month,day} =
    pad 4 (Int.toString year) ^ "-" ^ pad 2 (Int.toString month) ^ 
    "-" ^ pad 2 (Int.toString day)

fun return d = if check d then d else dateError (ppDate d)

fun addDays 0 d = return d
  | addDays i (d as {year,month,day}) =
    if i < 0 then subDays (~i) d
    else let val days = daysInMonth year month
             val n = days - day
         in if i <= n then return {year=year,month=month,day=day+i}
            else addDays (i-n-1)
                         (if month = 12 then {year=year+1,month=1,day=1}
                          else {year=year,month=month+1,day=1})
         end
and subDays 0 d = return d
  | subDays i (d as {year,month,day}) =
    if i < 0 then addDays (~i) d
    else if i < day then return {year=year,month=month,day=day-i}
    else let val (y,m) = if month = 1 then (year-1,12)
                         else (year,month-1)
             val d = daysInMonth y m
         in subDays (i-day) {year=y,month=m,day=d}
         end

fun compare ({year=y1,month=m1,day=d1}, {year=y2,month=m2,day=d2}) =
    if y1 < y2 then LESS
    else (if y1 = y2 then
            if m1 < m2 then LESS
            else if m1 = m2 then
              (if d1 < d2 then LESS
               else if d1 = d2 then EQUAL
               else GREATER)
            else GREATER
          else GREATER)
                 
(* computes day difference to go from d1 to d2 *)
fun dateDiff d1 d2 =
    case compare (d1,d2) of
        EQUAL => 0
      | GREATER => ~ (dateDiff d2 d1)
      | LESS =>   (* d1 < d2 *)
        let val {year=y1,month=m1,day=n1} = d1
            val {year=y2,month=m2,day=n2} = d2
        in
          if y1 = y2 then
            if m1 = m2 then n2 - n1
            else (* m2 > m1 *)
              let val d = daysInMonth y1 m1
              in d - n1 + 1 + dateDiff {year=y1,month=m1+1,day=1} d2
              end
          else (* y2 > y1 *)
            if m1 = 12 then
              daysInMonth y1 m1 + dateDiff {year=y1+1,month=1,day=n1} d2
            else
              daysInMonth y1 m1 + dateDiff {year=y1,month=m1+1,day=n1} d2
        end
(*            
          if n1 = n2 then
             if m1 = m2 then
               daysInYear (y2-1) + dateDiff d1 {year=y2-1,month=m2,day=n2}
             else if m2 > 1 then
               daysInMonth y2 (m2-1) + dateDiff d1 {year=y2,month=m2-1,day=n2}
             else daysInMonth (y2-1) 12 + dateDiff d1 {year=y2-1,month=12,day=n2}
           else if n2 > n1 then
             n2 - n1 + dateDiff d1 {year=y2,month=m2,day=n1}
           else (* n1 > n2 *)
             dateDiff d1 {year=y2,month=m2,day=n1} - (n1 - n2)
        end
*)


end

