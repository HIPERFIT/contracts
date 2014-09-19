signature DateUtil = sig
  type date                          (* abstract representation of a date *)
  exception DateError of string
  val ?        : string -> date      (* [?s] reads a date on the form YYYY-MM-DD from the string s; raises
                                      * DateError(msg) if s does not conform to the format. *)
  val addDays  : int -> date -> date
  val ppDate   : date -> string      (* [ppDate d] prints the date d on the form YYYY-MM-DD *)
  val dateDiff : date -> date -> int
  val compare  : date * date -> order
end
