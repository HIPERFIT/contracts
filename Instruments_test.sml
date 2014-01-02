structure Instruments_Test = struct
open Currency Contract Instruments
fun pr s c = print (s ^ ":\n " ^ ppContr c ^ "\n")              

val fxput = vanillaFx Put "F" "Nordea" (USD, SEK) 30E6 6.3 365
val () = pr "fxput" fxput

val touch = fxBarrierTouch "me" "you" EUR 1000.0 (EUR,USD) 1.0 Up (12*30)

val () = pr "touch" touch
end
