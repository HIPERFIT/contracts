load "Real";
load "ContractBase";
open ContractBase;
load "Contract";
open Contract;

(*
more JB notes about "trigger value extraction":

collecting triggers:

simpleTriggers : contr -> boolE list

triggers : contr -> (realE (obs, actually)* real list) list
                    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
it could be 
 (realE * real list) list ; grouped by the actual obs
 (string * int * real list) list ; grouped by the actual obs, decomposed
(X)
 (string * (int * real list) list ) list ; grouped by observable, then by day
 (int * (string * real list) list ) list ; grouped by day, then observable

Better: use a "time window" rather than single days.
            (merge becomes more complicated, well-understood)

Similar to (X) above:
 (string * ((int,int) * real list) list
           start,end

*)

fun mergeUniq xs [] = xs
  | mergeUniq [] ys = ys
  | mergeUniq (x::xs) (y::ys) 
    = case Real.compare (x,y) of
          LESS    => x :: mergeUniq xs (y::ys)
        | GREATER => y :: mergeUniq (x::xs) ys
        | EQUAL   => x :: mergeUniq xs ys

fun trMerge' (tr as (s,(d1,d2),vs), []) = [tr]
  | trMerge' (tr as (s,(d1,d2),vs), ((tr' as (s',(d1',d2'),vs')) :: trs))
  = if s = s' andalso d1 = d1' andalso d2 = d2'
    then (s,(d1,d2), mergeUniq vs vs') :: trs
    else tr' :: trMerge' (tr, trs)
  (* UNFINISHED, has to compare intervals and split into
several (2 or 3) resulting new ones:
        ---------------------  (3 resulting, overlap)
----------------------

----------------------         (3 resulting, inclusion)
   -------------

-------    -------             (2 resulting, easy)

*)

val trMerge = foldl trMerge'

(* triggersExp is where new triggers are added: *)

(* returns a list of triggers (s,(t1,t2),vs) *)
fun triggersExp (t1,t2) (BinOp ("<", e1, Obs(s,d)))
  = ([(s,(t1+d,t2+d), [evalR emptyEnv e1])] handle Fail _ => [])
  | triggersExp (t1,t2) (BinOp ("<", Obs(s,d), e1)) 
    = ([(s,(t1+d,t2+d), [evalR emptyEnv e1])] handle Fail _ => [])
  | triggersExp (t1,t2) (BinOp ("|", e1, e2)) 
    = trMerge (triggersExp (t1,t2) e1) (triggersExp (t1,t2) e2)
  | triggersExp (t1,t2) (UnOp ("not", e1)) = triggersExp (t1,t2) e1
(* *)
  | triggersExp ts exp = []


(* triggers : (int,int) -> contr -> trigger list (see above)
       where (int,int) is start+end relative date, starting at (0,0),
       expanded any time a construct introduces a "duration"
*)
fun triggers _ (Zero) = []
  | triggers _ (TransfOne _) = []
  | triggers ts (Scale (_,c)) = triggers ts c
  | triggers ts (Both (c1,c2)) = trMerge (triggers ts c1) (triggers ts c2)
  | triggers (t1,t2) (Transl (i,c)) = triggers (t1+i, t2+i) c
  | triggers ts (Let (v,e,c))  
    = raise Fail "clunky: need to consider v=e everywhere. How? Issue with translate, need an environment..."
  | triggers (t1,t2) (If(e,c1,c2)) 
    = trMerge (triggersExp (t1,t2) e)
              (trMerge (triggers (t1,t2) c1) (triggers (t1,t2) c2))
  | triggers (t1,t2) (CheckWithin (e,d,c1,c2))
    = trMerge (triggersExp (t1,t2+d) e)
              (trMerge (triggers (t1,t2+d) c1) (triggers (t1+d, t2+d) c2))


(* copied *)
infix !+! !-! !*! !<! !=! !|! ;

load "Currency"; open Currency;

fun M n = n*30
fun Y n = n*360

(* Call option on "Carlsberg" stock *)
val equity = "Carlsberg"
val maturity = Y 1
val ex4if =
    let val strike = 50.0
        val nominal = 1000.0
        val obs = obs(equity,0)
    in scale(R nominal,
             transl(maturity,
                    iff (R strike !<! obs,
                         scale(obs !-! R strike,
                               transfOne(EUR,"you","me")),
                         zero)))
    end

fun mkOpt i s =
    let val strike = s
        val nominal = 1000.0
        val obs = obs(equity,0)
    in scale(R nominal,
             transl(i,
                    iff (R strike !<! obs,
                         scale(obs !-! R strike,
                               transfOne(EUR,"you","me")),
                         zero)))
    end

val test1 = all (List.tabulate (10, fn di => mkOpt 360 (40.0 + real di)))
val test2 = all (List.tabulate (10, fn i => mkOpt (10+i) 32.0))

