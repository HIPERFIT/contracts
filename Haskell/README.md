# Haskell smart contract eDSL

## Module structure

```
Contract.hs       -- with smart constructors (also for Expr module)

        Contract.Expr       -- expression types, p.printer, evaluation

        Contract.Type       -- contract type and p.printer
                            -- exporting constructors, for internal use

        Contract.Date       -- date library

        Contract.Instrument -- canned FX product functions

        Contract.Transform  -- simplification/evaluation, normal form

        Contract.Analysis   -- trigger extraction etc (?)
```
