module DASHI.Analysis.RiemannArithmeticCoercivity where

-- Converts an exact positive decomposition of the arithmetic side of the
-- Riemann explicit formula into a positive decomposition of its spectral side.
-- This is the central reusable target for a DASHI prime-side coercivity proof.

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.RiemannExplicitFormula
open import DASHI.Analysis.WeilPositivityCore

record ArithmeticPositiveDecomposition
  (space : WeilTestSpace)
  (formula : RiemannExplicitFormula space) : Set₁ where
  open WeilTestSpace space
  open RiemannExplicitFormula formula
  field
    coerciveCore : Test → Scalar
    nonnegativeRemainder : Test → Scalar

    arithmeticDecomposition :
      (f : Test) → admissible f →
      arithmeticForm f
      ≡
      (coerciveCore f +S nonnegativeRemainder f)

    corePositive :
      (f : Test) → admissible f → nonnegative (coerciveCore f)

    remainderPositive :
      (f : Test) → admissible f →
      nonnegative (nonnegativeRemainder f)

arithmeticToSpectralDecomposition :
  (space : WeilTestSpace) →
  (formula : RiemannExplicitFormula space) →
  ArithmeticPositiveDecomposition space formula →
  WeilPositiveDecomposition space formula
arithmeticToSpectralDecomposition space formula arithmetic = record
  { coerciveCore = ArithmeticPositiveDecomposition.coerciveCore arithmetic
  ; nonnegativeRemainder =
      ArithmeticPositiveDecomposition.nonnegativeRemainder arithmetic
  ; decomposition = spectralDecomposition
  ; corePositive = ArithmeticPositiveDecomposition.corePositive arithmetic
  ; remainderPositive =
      ArithmeticPositiveDecomposition.remainderPositive arithmetic
  }
  where
  spectralDecomposition :
    (f : WeilTestSpace.Test space) →
    WeilTestSpace.admissible space f →
    RiemannExplicitFormula.spectralZeroForm formula f
    ≡
    (WeilTestSpace._+S_ space
      (ArithmeticPositiveDecomposition.coerciveCore arithmetic f)
      (ArithmeticPositiveDecomposition.nonnegativeRemainder arithmetic f))
  spectralDecomposition f admissibleF =
    ≡-trans
      (≡-sym
        (RiemannExplicitFormula.explicitFormula formula f admissibleF))
      (ArithmeticPositiveDecomposition.arithmeticDecomposition arithmetic
        f admissibleF)

arithmeticCoercivityImpliesWeilPositivity :
  (space : WeilTestSpace) →
  (formula : RiemannExplicitFormula space) →
  ArithmeticPositiveDecomposition space formula →
  (f : WeilTestSpace.Test space) →
  WeilTestSpace.admissible space f →
  WeilTestSpace.nonnegative space
    (RiemannExplicitFormula.spectralZeroForm formula f)
arithmeticCoercivityImpliesWeilPositivity space formula arithmetic =
  decompositionImpliesWeilPositivity space formula
    (arithmeticToSpectralDecomposition space formula arithmetic)
