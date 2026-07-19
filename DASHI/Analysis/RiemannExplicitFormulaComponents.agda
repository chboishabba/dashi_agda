module DASHI.Analysis.RiemannExplicitFormulaComponents where

-- Component-wise constructor for the Riemann explicit formula.  The arithmetic
-- decomposition becomes definitional; only the genuine equality with the
-- spectral zero form remains a supplied theorem.

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.RiemannExplicitFormula

record ExplicitFormulaComponents (space : WeilTestSpace) : Set₁ where
  open WeilTestSpace space
  field
    primePowerTerm : Test → Scalar
    archimedeanGammaTerm : Test → Scalar
    poleTerm : Test → Scalar
    trivialZeroTerm : Test → Scalar
    spectralZeroForm : Test → Scalar

    PrimePowerTermDefined : Test → Set
    ArchimedeanGammaTermDefined : Test → Set
    PoleTermDefined : Test → Set
    TrivialZeroTermDefined : Test → Set
    SpectralZeroSumDefined : Test → Set
    SumIntegralInterchangesJustified : Test → Set

    primePowerTermDefined :
      (f : Test) → admissible f → PrimePowerTermDefined f
    archimedeanGammaTermDefined :
      (f : Test) → admissible f → ArchimedeanGammaTermDefined f
    poleTermDefined :
      (f : Test) → admissible f → PoleTermDefined f
    trivialZeroTermDefined :
      (f : Test) → admissible f → TrivialZeroTermDefined f
    spectralZeroSumDefined :
      (f : Test) → admissible f → SpectralZeroSumDefined f
    sumIntegralInterchangesJustified :
      (f : Test) → admissible f →
      SumIntegralInterchangesJustified f

componentArithmeticForm :
  (space : WeilTestSpace) →
  ExplicitFormulaComponents space →
  WeilTestSpace.Test space →
  WeilTestSpace.Scalar space
componentArithmeticForm space components f =
  WeilTestSpace._+S_ space
    (ExplicitFormulaComponents.primePowerTerm components f)
    (WeilTestSpace._+S_ space
      (ExplicitFormulaComponents.archimedeanGammaTerm components f)
      (WeilTestSpace._+S_ space
        (ExplicitFormulaComponents.poleTerm components f)
        (ExplicitFormulaComponents.trivialZeroTerm components f)))

record ExplicitFormulaComponentIdentity
  (space : WeilTestSpace)
  (components : ExplicitFormulaComponents space) : Set₁ where
  open WeilTestSpace space
  field
    arithmeticEqualsSpectral :
      (f : Test) →
      admissible f →
      componentArithmeticForm space components f
      ≡
      ExplicitFormulaComponents.spectralZeroForm components f

componentsToRiemannExplicitFormula :
  (space : WeilTestSpace) →
  (components : ExplicitFormulaComponents space) →
  ExplicitFormulaComponentIdentity space components →
  RiemannExplicitFormula space
componentsToRiemannExplicitFormula space components identity = record
  { primePowerTerm =
      ExplicitFormulaComponents.primePowerTerm components
  ; archimedeanGammaTerm =
      ExplicitFormulaComponents.archimedeanGammaTerm components
  ; poleTerm = ExplicitFormulaComponents.poleTerm components
  ; trivialZeroTerm =
      ExplicitFormulaComponents.trivialZeroTerm components
  ; arithmeticForm = componentArithmeticForm space components
  ; spectralZeroForm =
      ExplicitFormulaComponents.spectralZeroForm components
  ; PrimePowerTermDefined =
      ExplicitFormulaComponents.PrimePowerTermDefined components
  ; ArchimedeanGammaTermDefined =
      ExplicitFormulaComponents.ArchimedeanGammaTermDefined components
  ; PoleTermDefined =
      ExplicitFormulaComponents.PoleTermDefined components
  ; TrivialZeroTermDefined =
      ExplicitFormulaComponents.TrivialZeroTermDefined components
  ; SpectralZeroSumDefined =
      ExplicitFormulaComponents.SpectralZeroSumDefined components
  ; SumIntegralInterchangesJustified =
      ExplicitFormulaComponents.SumIntegralInterchangesJustified components
  ; primePowerTermDefined =
      ExplicitFormulaComponents.primePowerTermDefined components
  ; archimedeanGammaTermDefined =
      ExplicitFormulaComponents.archimedeanGammaTermDefined components
  ; poleTermDefined =
      ExplicitFormulaComponents.poleTermDefined components
  ; trivialZeroTermDefined =
      ExplicitFormulaComponents.trivialZeroTermDefined components
  ; spectralZeroSumDefined =
      ExplicitFormulaComponents.spectralZeroSumDefined components
  ; sumIntegralInterchangesJustified =
      ExplicitFormulaComponents.sumIntegralInterchangesJustified components
  ; arithmeticDecomposition = λ f admissibleF → refl
  ; explicitFormula =
      ExplicitFormulaComponentIdentity.arithmeticEqualsSpectral identity
  }
