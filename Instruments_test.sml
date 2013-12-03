structure Instruments_Test = struct
open Currency Contract Instruments
fun pr s c = print (s ^ ":\n " ^ ppContr c ^ "\n")              

val fxput = vanillaFx Put "F" "Nordea" (USD, SEK) 30E6 6.3 365
val () = pr "fxput" fxput
end
