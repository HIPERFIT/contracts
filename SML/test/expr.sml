
infix  7  !*!
infix  6  !+! !-!
infix  5  !|!
infix  4  !=! !<!

open ContractSafe

fun etestE s e f E =
    Utest.testPP ppExp s e (fn () =>
                               let val e = f()
                               in simplifyExp E e
                               end)

fun etest s e f = etestE s e f emptyEnv

val () = etest "test !+! - i" (I 4) (fn () => I 3 !+! I 1)
val () = etest "test !+! - r" (R 4.0) (fn () => R 3.0 !+! R 1.0)

val () = etest "test !-! - i" (I 4) (fn () => I 5 !-! I 1)
val () = etest "test !-! - r" (R 4.0) (fn () => R 5.0 !-! R 1.0)

val () = etest "test !*! - i" (I 6) (fn () => I 3 !*! I 2)
val () = etest "test !*! - r" (R 6.0) (fn () => R 3.0 !*! R 2.0)

val () = etest "test !<! - rt" (B true) (fn () => R 2.0 !<! R 3.0)
val () = etest "test !<! - it" (B true) (fn () => I 2 !<! I 3)
val () = etest "test !<! - rf" (B false) (fn () => R 4.0 !<! R 3.0)
val () = etest "test !<! - rfe" (B false) (fn () => R 3.0 !<! R 3.0)
val () = etest "test !<! - if" (B false) (fn () => I 4 !<! I 3)
val () = etest "test !<! - ife" (B false) (fn () => I 3 !<! I 3)

val () = etest "test !=! - it" (B true) (fn () => I 4 !=! I 4)
val () = etest "test !=! - if" (B false) (fn () => I 4 !=! I 3)
val () = etest "test !=! - rt" (B true) (fn () => R 4.0 !=! R 4.0)
val () = etest "test !=! - rf" (B false) (fn () => R 4.0 !=! R 3.0)
val () = etest "test !=! - bt" (B true) (fn () => B true !=! B true)
val () = etest "test !=! - bf" (B false) (fn () => B true !=! B false)

val () = etest "test max - rfst" (R 45.0) (fn () => max(R 45.0, R 34.0))
val () = etest "test max - rsnd" (R 45.0) (fn () => max(R 21.0, R 45.0))
val () = etest "test min - rfst" (R 34.0) (fn () => min(R 45.0, R 34.0))
val () = etest "test min - rsnd" (R 21.0) (fn () => min(R 21.0, R 45.0))
val () = etest "test max - ifst" (I 45) (fn () => max(I 45, I 34))
val () = etest "test max - isnd" (I 45) (fn () => max(I 21, I 45))
val () = etest "test min - ifst" (I 34) (fn () => min(I 45, I 34))
val () = etest "test min - isnd" (I 21) (fn () => min(I 21, I 45))

val () = etest "test !|! - t" (B true) (fn () => B true !|! B true)
val () = etest "test !|! - tfst" (B true) (fn () => B true !|! B false)
val () = etest "test !|! - tsnd" (B true) (fn () => B false !|! B true)
val () = etest "test !|! - f" (B false) (fn () => B false !|! B false)

val () = etest "test not - t" (B true) (fn () => not(B false))
val () = etest "test not - f" (B false) (fn () => not(B true))

val () = etest "test iff - t" (I 34) (fn () => ifExpr(B true,I 33 !+! I 1, I 22))
val () = etest "test iff - f" (I 22) (fn () => ifExpr(not(B true),I 33 !+! I 1, I 22))

val () = etest "test pair" (I 34) (fn () => snd(fst(pair(pair(I 23,I 34),R 32.0))))

fun f v = v !+! I 1

val () = etest "test acc - i0" (I 44) (fn () => acc(f,0,I 44))
val () = etest "test acc - i3" (I 4) (fn () => acc(f,3,I 1))

fun f x = pair(fst x !+! obs("C",0),
               snd x !+! I 1)

val E = foldl(fn ((i,r),e) => addFix(("C",i,r),e)) emptyEnv [(0,1.0),(1,2.0),(2,3.0),(3,4.0),(4,5.0)]
val () = etestE "test acc - avg" (pair(R 15.0,I 5)) (fn () => acc(f,5,pair(R 0.0,I 0))) E

val E' = foldl(fn ((i,r),e) => addFix(("C",i,r),e)) emptyEnv [(0,1.0),(1,2.0),(2,3.0),(3,4.0)]
val () = etestE "test acc - avg2" (pair(R 10.0 !+! obs("C",4),I 5)) (fn () => acc(f,5,pair(R 0.0,I 0))) E'

fun carl n = (obs ("Carlsberg",0) !<! R n)

fun h e = hashExp ([], e, 0)

val () = Utest.testPP IntInf.toString "hashExp1" 8 (fn () => h (I 3))
val () = Utest.testPP IntInf.toString "hashExp2" 8 (fn () => h (carl 1.0))
val () = Utest.testPP IntInf.toString "hashExp2" 8 (fn () => h (carl 0.0))

