structure Currency = struct
datatype cur = EUR | DKK | SEK | USD | GBP | JPY
fun ppCur EUR = "EUR"
  | ppCur DKK = "DKK"
  | ppCur SEK = "SEK"
  | ppCur USD = "USD"
  | ppCur GBP = "GBP"
  | ppCur JPY = "JPY"
end
