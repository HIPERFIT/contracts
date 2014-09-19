(* Date *)
structure SimpleDate (* : sig
type date
exception Date
val fromString : string -> date
val toString : date -> string
val diff : date -> date -> int
val compare : date * date -> order
end *) =
struct
 type date = {year: int, month:int, day:int}
 exception Date
 fun fromString s =
     {year = valOf (Int.fromString(String.substring (s,0,4))),
      month = valOf (Int.fromString(String.substring (s,5,2))),
      day = valOf (Int.fromString(String.substring (s,8,2)))}
     handle _ => raise Date
 fun padl n s = 
     if n <= String.size s then s
     else padl n ("0" ^ s)
 fun toString {year,month,day} =
     padl 4 (Int.toString year) ^ "-" ^
     padl 2 (Int.toString month) ^ "-" ^
     padl 2 (Int.toString day)
 fun days {year,month,day} =
     360 * (year - 1) + 30 * (month - 1) + day - 1
 fun diff d1 d2 =
     days d1 - days d2
 fun compare ({year=y1,month=m1,day=d1},
              {year=y2,month=m2,day=d2}) =
     if y1 < y2 then LESS
     else 
       if y1 = y2 then
         if m1 < m2 then LESS
         else 
           if m1 = m2 then
             if d1 < d2 then LESS
             else 
               if d1 = d2 then EQUAL
               else GREATER
           else GREATER
       else GREATER
end
