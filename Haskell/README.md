# Haskell smart contract eDSL

To run tests, install [Stack](https://haskellstack.org/) and run:

```
$ stack test
```

## Module overview

- [Contract][src/Contract.hs]
  - [Contract.Expr][src/Contract/Expr.hs]: Expression type + pretty-printing function + evaluation
  - [Contract.ExprIO][src/Contract/ExprIO.hs]: A pretty-printing function
  - [Contract.Type][src/Contract/Type.hs]: Contract type
  - [Contract.Date][src/Contract/Date.hs]: Date type
  - [Contract.FXInstrument][src/Contract/FXInstrument.hs]: Canned FX product functions
  - [Contract.Transform][src/Contract/Transform.hs]: Simplification/evaluation, normal form
  - [Contract.Analysis][src/Contract/Analysis.hs]: Trigger extraction
  - [Contract.Hash][src/Contract/Hash.hs]: Utility functions for hashing expressions and contracts
  - [Contract.Environment][src/Contract/Environment.hs]: A partial mapping alike Data.Map.
