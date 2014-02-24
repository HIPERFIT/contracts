module Contract.Type
    ( Contract -- no constructors exported
    , Days, Party
    , transl -- smart constructors instead
    ) where

import Contract.Expr

type Days = Int
type Party = String

data Contract = Zero
              | Transfer Party Party Currency
              | Transl Days Contract 
              | Both Contract Contract
              -- ...
                deriving (Eq,Show)

transl :: Int -> Contract -> Contract
transl d c | d < 0 = error "transl: negative time"
transl 0 c = c
transl _ Zero = Zero
transl d (Transl d' c) = Transl (d+d') c
transl d c = Transl d c

