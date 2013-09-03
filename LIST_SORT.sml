(** List sort operations. *)
signature LIST_SORT =
  sig
    val sort   : ('a * 'a -> order) -> 'a list -> 'a list
    val sorted : ('a * 'a -> order) -> 'a list -> bool
  end
