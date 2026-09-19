module DASHI.Moonshine.JInvariantEisensteinBishopRadiusWeldValidation where

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Moonshine.JInvariantEisensteinBishopMajorantSeriesExact as Majorant
import DASHI.Moonshine.JInvariantEisensteinBishopRadiusWeldExact as P

compileRadiusWeldRegression :
  ∀ {LegacyRadius : Set}
    {_≈B_ : LegacyRadius → BishopReal.ℝ → Set}
    {literalRadius : LegacyRadius} →
  (weld : P.LiteralRadiusBishopWeld _≈B_ literalRadius) →
  P.EisensteinBishopMajorantReceipt _≈B_ literalRadius weld
compileRadiusWeldRegression = P.compileEisensteinBishopMajorants

e4ReceiptRegression :
  ∀ {LegacyRadius : Set}
    {_≈B_ : LegacyRadius → BishopReal.ℝ → Set}
    {literalRadius : LegacyRadius}
    (weld : P.LiteralRadiusBishopWeld _≈B_ literalRadius) →
  BishopSequence.SeriesOf_ConvergesAbsolutely
    (Majorant.e4MajorantTerm (P.bishopRadius weld))
e4ReceiptRegression weld =
  P.e4AbsoluteConvergence
    (P.compileEisensteinBishopMajorants weld)

e6ReceiptRegression :
  ∀ {LegacyRadius : Set}
    {_≈B_ : LegacyRadius → BishopReal.ℝ → Set}
    {literalRadius : LegacyRadius}
    (weld : P.LiteralRadiusBishopWeld _≈B_ literalRadius) →
  BishopSequence.SeriesOf_ConvergesAbsolutely
    (Majorant.e6MajorantTerm (P.bishopRadius weld))
e6ReceiptRegression weld =
  P.e6AbsoluteConvergence
    (P.compileEisensteinBishopMajorants weld)
