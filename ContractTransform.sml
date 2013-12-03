structure ContractTransform = struct

local open Currency Contract ContractBase in

infix !+! !*!

(* find out if two contracts are the same. Assumes normalised, i.e. same
   constructor structure and ordered components *)
fun equal (c1,c2) = case (c1,c2) of
                      (Zero, Zero) => true
                    | (TransfOne (cur1,x1,y1),TransfOne (cur2,x2,y2))
                      => cur1 = cur2 andalso x1 = x2 andalso y1 = y2
                    | (Scale (s1,c1),Scale (s2,c2))
                      => eqExp(s1, s2) andalso equal (c1,c2)
                    | (Transl (d1,c1),Transl (d2,c2))
                      => eqExp(d1,d2) andalso equal (c1,c2)
                    | (If (b1,x1,y1),If (b2,x2,y2))
                      => eqExp(b1,b2) andalso equal (x1,x2) andalso equal (y1,y2)
                    | (CheckWithin (b1,i1,x1,y1),CheckWithin (b2,i2,x2,y2))
                      => eqExp(b1,b2) andalso eqExp(i1,i2) andalso 
                         equal (x1,x2) andalso equal (y1,y2)
                    | (Both(c1,c2), Both(c1',c2')) => equal (c1,c1') andalso equal (c2,c2')
                      (* assumes pairs are sorted! Need to define ordering *)
                    | (_,_) => false

(* this can be quite arbitrary... here implementing an ordering that
   follows the normalisation (inside to outside), 

     TransfOne < Scale < All < If < CheckWithin < Transl

   and order by components within. Requires compare on expressions
   (with same type) and on currencies.
*)
fun notEqual EQUAL = false
  | notEqual _     = true

(* some of this requires compare for expressions, commented out for now *)
fun compare (TransfOne (c1,x1,y1), TransfOne (c2,x2,y2)) =
    hd (List.filter notEqual [(* compare (c1,c2),*) 
                              String.compare (x1^y1,x2^y2)] @ [EQUAL])
  | compare (TransfOne _, _) = LESS
  | compare (_, TransfOne _) = GREATER
  | compare (Scale (s1,c1), Scale (s2,c2)) =
    hd (List.filter notEqual [compare (c1,c2)
                           (*, compare (s1,s2)*)] @ [EQUAL])
  | compare (Scale _, _) = LESS
  | compare (_, Scale _) = GREATER
  | compare (Both(c1,c2), Both(c1',c2')) =
    (case compare (c1, c1') of
         LESS => LESS
       | GREATER => GREATER
       | EQUAL => compare(c2,c2'))
  | compare (Both _, _) = LESS
  | compare (_, Both _) = GREATER
  | compare (If(b1,x1,y1),If(b2,x2,y2)) =
    hd (List.filter notEqual [compare (x1,x2), 
                              compare (y1,y2) 
                           (*, compare (b1,b2)*)] @ [EQUAL])
  | compare (If _, _) = LESS
  | compare (_, If _) = GREATER
  | compare (CheckWithin (b1,i1,x1,y1),CheckWithin (b2,i2,x2,y2)) =
    hd (List.filter notEqual [compare (x1,x2), compare (y1,y2) 
                           (*, compare (b1,b2), compare (i1,i2)*)] @ [EQUAL])
  | compare (CheckWithin _, _) = LESS
  | compare (_, CheckWithin _) = GREATER
  | compare (Transl (i1,c1), Transl (i2,c2)) =
    hd (List.filter notEqual [compare (c1,c2)(*, compare (i1,i2)*)] @ [EQUAL])
  | compare (_,_) = raise Fail "Dude! This should never happen!"

(* Normalisation... Continue this one, many jobs to do here:
o gather Transl outside of If/Check, All and Scale inside 
o multiply Scale, add Transl, cutting them when empty below 
o sort the list inside "All" nodes (for comparisons, see above)
*)
fun normalise (Transl (i,c)) = (case normalise c of
   (* aggregate several Transl *)   Transl (i',c') => Transl (i !+! i', c')
                                  | other => Transl (i,other))
  | normalise a = a

(* routine assumes a is normalised contract and applies no own
   optimisations except removing empty branches *)
fun removeParty_ (p : string) ( a : contr) =
    let fun remv c = 
                case c of 
                    TransfOne (_,p1,p2) => if p = p1 orelse p = p2 
                                           then zero else c
                  | Scale (s,c')  => (case remv c' of
                                          Zero => zero
                                        | other  => Scale (s,other))
                  | Transl (d,c') => (case remv c' of
                                          Zero => zero
                                        | other  => Transl (d, other))
                  | Both(c1,c2) => Both (remv c1, remv c2)
                  | Zero => Zero
                  | If (b,c1,c2)  => (case (remv c1, remv c2) of
                                          (Zero,Zero) => zero
                                        | (c1', c2')  => If (b,c1',c2'))
                  | CheckWithin (b,i,c1,c2) => 
                             (case (remv c1, remv c2) of
                                  (Zero,Zero) => zero
                                | (c1', c2')  => CheckWithin (b,i,c1',c2'))
    in normalise (remv a)
    end

(* this routine should work with any contract *)
fun removeParty p a = removeParty p (normalise a)

(* replaces p1 by p2 in all contracts inside a. Assumes normalised a.
   Could try to aggregate flows between same parties afterwards *)
fun mergeParties_ (p1 : party) (p2 : party) (a : contr) =
    let fun merge c = 
                case c of 
                    Zero => zero
                  | TransfOne (cur,pA,pB) =>
                          if pA = p1 then 
                              if pB = p1 orelse pB = p2 then zero
                              else TransfOne (cur,p2,pB)
                          else 
                          if pB = p1 then 
                              if pA = p2 then zero
                              else TransfOne (cur,p2,pB)
                          else c
                  | Scale (s,c')  => (case merge c' of
                                          Zero => zero
                                        | other  => Scale (s,other))
                  | Transl (i,c') => (case merge c' of
                                          Zero => zero
                                        | other  => Transl (i,other))
                  | Both(c1,c2) => Both (merge c1,merge c2)
                  (* merging parties can render conditional branches
                     equivalent (i.e. same normalised contract) *)
                  | If (b,c1,c2)  => (case (normalise (merge c1),
                                            normalise (merge c2)) of
                                          (Zero, Zero) => zero
                                        | (c1', c2')      =>
                                          if equal (c1',c2') then c1'
                                          else If (b,c1',c2'))
                  | CheckWithin (b,i,c1,c2) =>
                             (case (normalise (merge c1),
                                    normalise (merge c2)) of
                                  (Zero, Zero) => zero
                                | (c1', c2')      =>
                                  if equal (c1',c2') then c1'
                                  else CheckWithin (b,i,c1',c2'))
    in normalise (merge a)
    end 

(* replaces p1 by p2 in all contracts inside a*)
fun mergeParties p1 p2 a = mergeParties p1 p2 (normalise a)

end
end
