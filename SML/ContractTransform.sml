structure ContractTransform = struct

local open Currency Contract ContractBase in

infix !+! !*! !-!

(* Contract normalisation:
o gather Transl outside of If, CheckWithin. Both and Scale inside 
o multiply Scale, add Transl, cutting them when empty below 

TODO: use (temporary) tag to avoid repeated traversals!!!
*)
fun normalise (Transl (i,c)) = (case normalise c of
   (* aggregate several Transl *)   Transl (i',c') => transl (i + i', c')
                                  | Zero => Zero
                                  | other => transl (i,other))
  | normalise (If (b,c1,c2)) = 
    (case (normalise c1,normalise c2) of 
         (Zero,Zero) => Zero
         (* lift Transl constr.s to top *) 
       | (Transl (i1,c1'),Transl (i2,c2'))
         => if i1 =i2 then transl(i1, normalise (iff (b, c1', c2')))
            else let val iMin = Int.min (i1, i2)
                     val i1' = i1 - iMin
                     val i2' = i2 - iMin
                 in transl(iMin, iff (translExp (b, ~iMin),
                                      transl(i1', c1'), 
                                      transl(i2', c2')))
                 end
       | (Transl (i1,c1'),Zero) => transl (i1, normalise (iff (b, c1', zero)))
       | (Zero,Transl (i2,c2')) => transl (i2, normalise (iff (b, zero, c2')))
       | (c1' as If(b',c11,_),c2') => 
         if eqExp (b, b') then normalise (iff (b, c11, c2'))
                          else iff (b, c1', c2')
       | (c1',c2' as If(b',_,c22)) => 
         if eqExp (b, b') then normalise (iff (b, c1', c22))
                          else iff (b, c1', c2')
       | (c1' as CheckWithin(b',_,c11,_),c2') => 
         if eqExp (b, b') then normalise (iff (b, c11, c2'))
                          else iff (b, c1', c2')
       | (c1',c2') => iff (b, c1', c2'))
  | normalise (CheckWithin (b, i, c1, c2)) =
    (case (normalise c1, normalise c2) of
         (Zero,Zero) => Zero
         (* lift Transl constr.s to top *)
       | (Transl (i1,c1'),Transl (i2,c2'))
         => if i1 = i2 then transl(i1, checkWithin (translExp (b, ~i1), i, c1', c2'))
            else let val iMin = Int.min (i1, i2)
                     val i1' = i1 - iMin
                     val i2' = i2 - iMin
                     val b'  = translExp (b, ~iMin)
                 in transl(iMin, checkWithin (b', i, transl(i1',c1'),
                                              transl(i2', c2')))
                 end
       | (Transl (i1,c1'),Zero) => transl (i1, checkWithin (translExp (b, ~i1), i, c1', zero))
       | (Zero,Transl (i2,c2')) => transl (i2, checkWithin (translExp (b, ~i2), i, zero, c2'))
       | (c1' as If(b',c11,_),c2') => 
         if eqExp (b, b') then normalise (checkWithin (b, i, c11, c2'))
                          else checkWithin (b, i, c1', c2')
       | (c1',c2' as If(b',_,c22)) => 
         if eqExp (b, b') then normalise (checkWithin (b, i, c1', c22))
                          else checkWithin (b, i, c1', c2')
       | (c1' as CheckWithin(b',_,c11,_),c2') => 
         if eqExp (b, b') then normalise (checkWithin (b, i, c11, c2'))
                          else checkWithin (b, i, c1', c2')
       | (c1', c2') => checkWithin (b, i, c1', c2'))
  | normalise (Both (c1,c2)) =
    (case (normalise c1, normalise c2) of
         (Zero,Zero) => Zero
       | (Zero,c) => c
       | (c,Zero) => c
       (* lift Transl constr.s to top *)
       | (Transl (i1,c1'),Transl (i2,c2'))
         => if i1 = i2 then transl(i1, both (c1', c2'))
            else let val iMin = Int.min (i1, i2)
                     val i1' = i1 - iMin
                     val i2' = i2 - iMin
                 in transl(iMin, both (transl(i1',c1'), transl(i2', c2')))
                 end
       | (If(b1,c11,c12),If(b2,c21,c22)) 
         (* memo: maybe better to lift "Both" up, right below "Transl"?*)
         => if eqExp (b1,b2) then iff (b1, both (c11,c21), both (c12,c22))
            else both ( iff (b1,c11,c12), iff (b2, c21, c22))
       (* create right-bias (as constructor does) *)
       | (Both(c11,c12),c2) => normalise (both (c11,both (c12,c2)))
       | (c1', c2') => if eqContr (c1', c2') 
                       then normalise (scale (R 2.0,c1'))
                       else both (c1', c2'))
  | normalise (Scale (e, c)) =
    (case normalise c of
         Zero => Zero
       | Scale (e',c') => scale (e !*! e', c') (* aggregate scales  *)
       | Transl (i,c') =>
         transl (i, normalise (scale (e,c')))  (* transl to top     *)
       | If (e,c1,c2)  =>                      (* iff outside scale *)
         iff (e, normalise (scale (e,c1)), normalise (scale (e,c2)))
       | CheckWithin (e,i,c1,c2) =>
         checkWithin (e, i, 
                      normalise (scale (e,c1)), normalise (scale (e,c2)))
       | Both (c1,c2) => 
         (* repeated normalisation to merge chains of "scale" *)
         both (normalise (scale (e,c1)), normalise (scale (e,c2)))
       | other         => scale (e, other))
  (* leave let where they are (for now, could float them out) *)
  | normalise (Let (v,e,c1)) = (case normalise c1 of
                                    Zero => Zero
                                  | c1'  => Let (v,e, normalise c1'))
  (* zero and flows stay *)
  | normalise a = a

(* unrolling all CheckWithin constructors into a corresponding iff chain *)
fun unrollCWs (If(e,c1,c2))  = iff (e, unrollCWs c1, unrollCWs c2)
  | unrollCWs (Both (c1,c2)) = both (unrollCWs c1, unrollCWs c2)
  | unrollCWs Zero = zero
  | unrollCWs (Transl (i,c)) = transl (i, unrollCWs c)
  | unrollCWs (Scale (e,c))  = scale (e,unrollCWs c)
  | unrollCWs (TransfOne (c,p1,p2)) = TransfOne (c,p1,p2)
  | unrollCWs (CheckWithin (e,t,c1,c2)) =
    let fun check i = iff (translExp (e,i), transl (i,c1),
                           if i = t then transl (t,c2) else check (i+1))
    in check 0
    end
  | unrollCWs (Let (v,e,c1)) = Let (v,e,unrollCWs c1)

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
                  | Let (v,e,c1) => case remv c1 of
                                        Zero => Zero
                                      | c1'  => Let (v,e,c1')
    in normalise (remv a)
    end

(* this routine should work with any contract *)
fun removeParty p a = removeParty_ p (normalise a)

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
                                          if eqContr (c1',c2') then c1'
                                          else If (b,c1',c2'))
                  | CheckWithin (b,i,c1,c2) =>
                             (case (normalise (merge c1),
                                    normalise (merge c2)) of
                                  (Zero, Zero) => zero
                                | (c1', c2')      =>
                                  if eqContr (c1',c2') then c1'
                                  else CheckWithin (b,i,c1',c2'))
                  | Let (v,e,c1) => case merge c1 of
                                        Zero => Zero
                                      | c1'  => Let (v,e,c1')
    in normalise (merge a)
    end 

(* replaces p1 by p2 in all contracts inside a*)
fun mergeParties p1 p2 a = mergeParties p1 p2 (normalise a)

end
end
