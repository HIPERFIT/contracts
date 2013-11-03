(** List sort operations. *)
signature MYLIST_SORT =
  sig
    val sort   : ('a * 'a -> order) -> 'a list -> 'a list
    val sorted : ('a * 'a -> order) -> 'a list -> bool
  end
