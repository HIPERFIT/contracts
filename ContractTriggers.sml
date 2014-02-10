structure ContractTriggers = struct 

open ContractBase Contract;

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
  = if s = s' then 
  (* compares intervals and splits into several (2 or 3) resulting ones:
        ---------------------  (3 resulting, overlap)
----------------------

   -------------
----------------------         (3 resulting, inclusion)

-------    -------             (2 resulting, disjoint)

       -----------             (2 results, simple inclusion)
------------------

------|----- and vs = vs'      (merge opportunity)
*)
      (* merge opportunity. However, might be desirable to keep apart
        if vs = vs' andalso (d2 = d1'+1 orelse d1 = d2'+1)
        then trMerge' ((s, (Int.min (d1,d1'), Int.max (d2,d2')), vs), trs)
        else *)
        if d2 < d1' orelse d2' < d1 (* disjoint, continue merging *)
        then tr' :: trMerge' (tr, trs)
        else
            if d1 = d1'
            then if d2 = d2' (* identical ranges: *)
                 then (s,(d1,d2), mergeUniq vs vs') :: trs
                 else (* simple inclusion, and we know d2 <> d2' *)
                     let val vs'' = if d2 < d2' then vs' else vs
                         val lo   = Int.min (d2, d2')
                     in trMerge ((s,(d1,lo), mergeUniq vs vs') ::
                                 (s,(lo+1,Int.max (d2,d2')), vs'') :: trs)
                     end
            else if d2 = d2' (* simple inclusion, d1 <> d1' *)
             then let val vs'' = if d1 < d1' then vs else vs'
                      val hi   = Int.max (d1, d1')
                  in trMerge ((s,(Int.min (d1,d1'),hi), vs'') ::
                              (s,(hi+1,d2), mergeUniq vs vs') :: trs)
                  end
             else (* d1 <> d1', d2 <> d2' *)
                 if d1 < d1' andalso d2' < d2 (* inclusion of tr' *)
                 then trMerge ((s,(d1,d1'-1), vs) ::
                               (s,(d1',d2'), mergeUniq vs vs') ::
                               (s,(d2'+1,d2), vs) :: trs)
                 else if d1' < d1 andalso d2 < d2' (* inclusion of tr *)
                  then trMerge ((s,(d1',d1-1), vs') ::
                                (s,(d1,d2), mergeUniq vs vs') ::
                                (s,(d2+1,d2'), vs) :: trs)
                  else (* real overlap *)
                      let val v1s = if d1 < d1' then vs else vs'
                          val v2s = if d2 < d2' then vs' else vs
                          val (mid1,mid2) = (Int.max (d1,d1'),Int.min (d2,d2'))
                      in trMerge ((s,(Int.min (d1,d1'),mid1-1), v1s) ::
                                  (s,(mid1,mid2), mergeUniq vs vs') ::
                                  (s,(mid2+1,Int.max (d2,d2')), v2s) :: trs )
                      end 
    else tr' :: trMerge' (tr, trs) (* different observables *)
and trMerge ts = foldl trMerge' [] ts

(* triggersExp is where new triggers are added: *)

(* returns a list of triggers (s,(t1,t2),vs) *)
fun triggersExp (t1,t2) (BinOp ("<", e1, Obs(s,d)))
  = ([(s,(t1+d,t2+d), [evalR emptyEnv e1])] handle Fail _ => [])
  | triggersExp (t1,t2) (BinOp ("<", Obs(s,d), e1)) 
    = ([(s,(t1+d,t2+d), [evalR emptyEnv e1])] handle Fail _ => [])
  | triggersExp (t1,t2) (BinOp ("|", e1, e2)) 
    = trMerge ((triggersExp (t1,t2) e1) @ (triggersExp (t1,t2) e2))
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
  | triggers ts (Both (c1,c2)) = trMerge ((triggers ts c1) @ (triggers ts c2))
  | triggers (t1,t2) (Transl (i,c)) = triggers (t1+i, t2+i) c
  | triggers ts (Let (v,e,c))  
    = raise Fail "clunky: need to consider v=e everywhere. How? Issue with translate, need an environment..."
  | triggers (t1,t2) (If(e,c1,c2)) 
    = trMerge ((triggersExp (t1,t2) e) @
               (triggers (t1,t2) c1) @
               (triggers (t1,t2) c2))
  | triggers (t1,t2) (CheckWithin (e,d,c1,c2))
    = trMerge ((triggersExp (t1,t2+d) e) @
               (triggers (t1,t2+d) c1) @
               (triggers (t1+d, t2+d) c2))

fun ppTriggers     [] = ""
  | ppTriggers ((s,(i,j),vs)::rest) 
    = s ^ " from day " ^ Int.toString i ^ " to " ^ Int.toString j ^
      ": " ^ (String.concatWith ", " (map Real.toString vs)) ^
      "\n" ^ ppTriggers rest

(* *)


end
