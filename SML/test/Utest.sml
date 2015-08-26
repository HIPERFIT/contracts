structure Utest = struct

fun testPP pp s e f =
    let fun pr res = print (s ^ ": " ^ res ^ "\n")
    in let val e1 = f()
           val s1 = pp e1
           val s = pp e
       in if s1 = s then pr "OK" 
          else pr("ERR -\n  expected: " ^ s ^ "\n  got:      " ^ s1)
       end handle Fail s => pr ("EXN Fail(" ^ s ^ ")")
                | ? => pr ("EXN: " ^ General.exnMessage ?)
    end 

end
