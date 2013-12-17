
signature CONTRACT_MONAD = sig
  type 'a m
  val ret       : 'a -> 'a m
  val >>=       : 'a m * ('a -> 'b m) -> 'b m
  val >>        : unit m * 'b m -> 'b m
  val observe   : string -> Contract.realE m
  val transf    : Contract.realE * Contract.cur * Contract.party * Contract.party -> unit m
  val ifm       : Contract.boolE * 'a m * 'a m -> 'a m
  val wait      : int -> unit m
  val terminate : unit -> 'a m
  val skip      : unit m
  val toContr   : unit m -> Contract.contr
end

structure ContractMonad :> CONTRACT_MONAD =
struct
open Contract
type 'a m = ('a -> int -> contr) -> int -> contr
fun ret a k i = k a i
infix >>= >>
fun f >>= g = fn k => fn i =>
    f (fn a => fn i' => g a k i') i
fun f >> m = f >>= (fn _ => m)
fun observe s k i = k (obs(s,i)) i
fun transf (e, c, p1, p2) k i =
    both(scale(e,transfOne(c,p1,p2)), k () i)
fun ifm (b,m1,m2) k i = iff (b,m1 k i, m2 k i)
fun wait i' k i = transl(i', k () i)
fun terminate () k i = zero
val skip = ret ()
fun toContr m = m (fn _ => fn _ => zero) 0
end

open ContractMonad Contract Currency
infix >>= >> !<! !-!
val c = toContr
  (wait 2 >>
   wait 5 >>
   transf (R 1000.0, EUR, "me", "you") >>
   wait 10 >>
   transf (R 1005.0, EUR, "you", "me"))

val c2 = toContr
  (observe "Carlsberg" >>= (fn strike =>
   wait 30 >>
   observe "Carlsberg" >>= (fn c =>
   ifm(strike !<! c,
       transf(c !-! strike, DKK, "you", "me"),
       skip)
   )))
