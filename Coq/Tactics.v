(** [false_goal] replaces any goal by the goal [False]. 
    Contrary to the tactic [false] (below), it does not try to do
    anything else *)

Tactic Notation "false_goal" :=
  elimtype False.

(** [false_post] is the underlying tactic used to prove goals
    of the form [False]. In the default implementation, it proves
    the goal if the context contains [False] or an hypothesis of the
    form [C x1 .. xN  =  D y1 .. yM], or if the [congruence] tactic
    finds a proof of [x <> x] for some [x]. *) 

Ltac false_post :=
  solve [ assumption | discriminate | congruence ].

(** [false] replaces any goal by the goal [False], and calls [false_post] *)

Tactic Notation "false" :=
  false_goal; try false_post.

(** [tryfalse] tries to solve a goal by contradiction, and leaves
    the goal unchanged if it cannot solve it.
    It is equivalent to [try solve \[ false \]]. *)

Tactic Notation "tryfalse" :=
  try solve [ false ].

(** [tryfalse by tac /] is that same as [tryfalse] except that
    it tries to solve the goal using tactic [tac] if [assumption]
    and [discriminate] do not apply.
    It is equivalent to [try solve \[ false; tac \]]. 
    Example: [tryfalse by congruence/] *)

Tactic Notation "tryfalse" "by" tactic(tac) "/" :=
  try solve [ false; instantiate; tac ].


Ltac rewr_assumption := idtac; match goal with
                          | [R: _ = _ |- _ ] => first [rewrite R| rewrite <- R]
                        end.

Tactic Notation "rewr_assumption" "in" ident(H) := 
  idtac; match goal with
           | [R: _ = _ |- _ ] => first [rewrite R in H| rewrite <- R in H]
         end.


Ltac def_to_eq_sym X HX E :=
  assert (HX : E = X) by reflexivity; clearbody X.

Tactic Notation "cases" constr(E) "as" ident(H) :=
  let X := fresh "TEMP" in
  set (X := E) in *; def_to_eq_sym X H E;
  destruct X.

Tactic Notation "cases" constr(E) :=
  let H := fresh "Eq" in cases E as H.
