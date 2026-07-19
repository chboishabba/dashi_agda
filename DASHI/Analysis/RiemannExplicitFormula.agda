module DASHI.Analysis.RiemannExplicitFormula where

-- Exact arithmetic/spectral ownership for the Riemann explicit formula.
--
-- The decomposition fields prevent a future implementation from hiding the
-- prime-power, archimedean, pole, or trivial-zero terms behind one opaque
-- equality.  No inhabitant is supplied here.

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Analysis.WeilTestSpace

record RiemannExplicitFormula (space : WeilTestSpace) : Set₁ where
  open WeilTestSpace space
  field
    primePowerTerm : Test → Scalar
    archimedeanGammaTerm : Test → Scalar
    poleTerm : Test → Scalar
    trivialZeroTerm : Test → Scalar

    arithmeticForm : Test → Scalar
    spectralZeroForm : Test → Scalar

    primePowerTermDefined : (f : Test) → admissible f → Set
    archimedeanGammaTermDefined : (f : Test) → admissible f → Set
    poleTermDefined : (f : Test) → admissible f → Set
    trivialZeroTermDefined : (f : Test) → admissible f → Set
    spectralZeroSumDefined : (f : Test) → admissible f → Set
    sumIntegralInterchangesJustified : (f : Test) → admissible f → Set

    arithmeticDecomposition :
      (f : Test) → admissible f →
      arithmeticForm f
      ≡
      (primePowerTerm f +S
       (archimedeanGammaTerm f +S
        (poleTerm f +S trivialZeroTerm f)))

    explicitFormula :
      (f : Test) → admissible f →
      arithmeticForm f ≡ spectralZeroForm f
