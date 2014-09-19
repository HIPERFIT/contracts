signature CURRENCY = sig
  eqtype cur
  val EUR : cur
  val DKK : cur
  val SEK : cur
  val USD : cur
  val GBP : cur
  val JPY : cur
  val ppCur : cur -> string
end
