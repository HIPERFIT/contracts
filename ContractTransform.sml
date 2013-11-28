structure ContractTransform = struct

local open ContractTypes in

(* find out if two contracts are the same. Assumes normalised, i.e. same
   constructor structure and ordered components *)
fun equal (c1,c2) = case (c1,c2) of
                      (TransfOne (cur1,x1,y1),TransfOne (cur2,x2,y2))
                      => cur1 = cur2 andalso x1 = x2 andalso y1 = y2
                    | (Scale (s1,c1),Scale (s2,c2))
                      => s1 = s2 andalso equal (c1,c2)
                    | (Transl (d1,c1),Transl (d2,c2))
                      => d1 = d2 andalso equal (c1,c2)
                    | (If (b1,x1,y1),If (b2,x2,y2))
                      => b1 = b2 andalso equal (x1,x2) andalso equal (y1,y2)
                    | (CheckWithin (b1,i1,x1,y1),CheckWithin (b2,i2,x2,y2))
                      => b1 = b2 andalso i1 = i2 andalso 
                         equal (x1,x2) andalso equal (y1,y2)
                    | (All cs1, All cs2) 
                      => ListPair.all equal (cs1,cs2)
                      (* assumes lists are sorted! Need to define ordering *)
                    | (_,_) => false

fun cOrd (c1,c2) = raise Fail "dude! do it"

fun normalise a = a (* do this one later: many jobs to do here:
o gather Transl outside of If/Check, All and Scale inside 
o multiply Scale, add Transl, cutting them when empty below 
o sort the list inside "All" nodes (for comparisons, see above)
*)

(* routine assumes a is normalised contract and applies no own
   optimisations except removing empty branches *)
fun removeParty_ (p : string) ( a : contract) =
    let fun remv c = 
                case c of 
                    TransfOne (_,p1,p2) => if p = p1 orelse p = p2 
                                           then emp else c
                  | Scale (s,c')  => (case remv c' of
                                          All [] => emp
                                        | other  => Scale (s,other))
                  | Transl (d,c') => (case remv c' of
                                          All [] => emp
                                        | other  => Transl (d, other))
                  | All cs => All (List.map remv cs)
                  | If (b,c1,c2)  => (case (remv c1, remv c2) of
                                          (All [],All []) => emp
                                        | (c1', c2')      => If (b,c1',c2'))
                  | Iter _ => c (* could symbolically simplify "contract" if it
                                   was a symbolic repr. of var -> "contract" *)
                  | CheckWithin (b,i,c1,c2) => 
                             (case (remv c1, remv c2) of
                                  (All [],All []) => emp
                                | (c1', c2')      => CheckWithin (b,i,c1',c2'))
    in normalise (remv a)
    end

(* this routine should work with any contract *)
fun removeParty p a = removeParty p (normalise a)

(* replaces p1 by p2 in all contracts inside a. Assumes normalised a.
   Could try to aggregate flows between same parties afterwards *)
fun mergeParties_ (p1 : party) (p2 : party) (a : contract) =
    let fun merge c = 
                case c of 
                    TransfOne (cur,pA,pB) =>
                          if pA = p1 then 
                              if pB = p1 orelse pB = p2 then emp
                              else TransfOne (cur,p2,pB)
                          else 
                          if pB = p1 then 
                              if pA = p2 then emp
                              else TransfOne (cur,p2,pB)
                          else c
                  | Scale (s,c')  => (case merge c' of
                                          All [] => All []
                                        | other  => Scale (s,other))
                  | Transl (i,c') => (case merge c' of
                                          All [] => All []
                                        | other  => Transl (i,other))
                  | All cs => All (List.map merge cs)
                  (* merging parties can render conditional branches
                     equivalent (i.e. same normalised contract) *)
                  | If (b,c1,c2)  => (case (normalise (merge c1),
                                            normalise (merge c2)) of
                                          (All [],All []) => emp
                                        | (c1', c2')      =>
                                          if equal (c1',c2') then c1'
                                          else If (b,c1',c2'))
                  | CheckWithin (b,i,c1,c2) =>
                             (case (normalise (merge c1),
                                    normalise (merge c2)) of
                                  (All [],All []) => emp
                                | (c1', c2')      =>
                                  if equal (c1',c2') then c1'
                                  else CheckWithin (b,i,c1',c2'))
                  | Iter _ => raise Fail "Iter"
    in normalise (merge a)
    end 

(* replaces p1 by p2 in all contracts inside a*)
fun mergeParties p1 p2 a = mergeParties p1 p2 (normalise a)

end
end
