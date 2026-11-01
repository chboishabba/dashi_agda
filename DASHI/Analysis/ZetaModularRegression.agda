module DASHI.Analysis.ZetaModularRegression where

-- Concrete plumbing regression for the modular zeta lane.
--
-- This instantiates the generic scalar/test algebra and explicit-formula
-- component constructor.  It is not an analytic zeta model and cannot inhabit
-- any Millennium assembly.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Nat using (_+_; _*_)
open import DASHI.TrackedPrimes using (SSP; toNat)
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.RiemannPrimePowerArithmetic
open import DASHI.Analysis.RiemannExplicitFormula
open import DASHI.Analysis.RiemannExplicitFormulaComponents

------------------------------------------------------------------------
-- Toy ordered scalar/test carrier
------------------------------------------------------------------------

toyWeilSpace : WeilTestSpace
toyWeilSpace = record
  { Scalar = Nat
  ; Test = Nat
  ; TransformValue = Nat
  ; zeroS = zero
  ; _+S_ = _+_
  ; nonnegative = λ n → ⊤
  ; nonnegativeZero = tt
  ; nonnegativeAdd = λ xNonnegative yNonnegative → tt
  ; nonnegativeTransport = λ equality xNonnegative → tt
  ; admissible = λ f → ⊤
  ; involution = λ f → f
  ; transform = λ f → f
  ; transformDefined = λ f admissibleF → tt
  ; involutionAdmissible = λ f admissibleF → tt
  }

toyPrimePowerKernel : PrimePowerKernel toyWeilSpace
toyPrimePowerKernel = record
  { _*S_ = _*_
  ; logPrimeWeight = toNat
  ; sampleAtNat = λ f n → f + n
  }

zeroExponentTerms :
  (f : Nat) →
  (p : SSP) →
  sumExponentTerms toyWeilSpace toyPrimePowerKernel zero f p
  ≡ zero
zeroExponentTerms f p = refl

oneExponentUnfolds :
  (f : Nat) →
  (p : SSP) →
  sumExponentTerms toyWeilSpace toyPrimePowerKernel (suc zero) f p
  ≡
  (weightedPrimePowerTerm
    toyWeilSpace toyPrimePowerKernel f p zero
   + zero)
oneExponentUnfolds f p = refl

------------------------------------------------------------------------
-- Definitional explicit-formula component assembly
------------------------------------------------------------------------

toyComponents : ExplicitFormulaComponents toyWeilSpace
toyComponents = record
  { primePowerTerm = λ f → zero
  ; archimedeanGammaTerm = λ f → zero
  ; poleTerm = λ f → zero
  ; trivialZeroTerm = λ f → zero
  ; spectralZeroForm = λ f → zero
  ; PrimePowerTermDefined = λ f → ⊤
  ; ArchimedeanGammaTermDefined = λ f → ⊤
  ; PoleTermDefined = λ f → ⊤
  ; TrivialZeroTermDefined = λ f → ⊤
  ; SpectralZeroSumDefined = λ f → ⊤
  ; SumIntegralInterchangesJustified = λ f → ⊤
  ; primePowerTermDefined = λ f admissibleF → tt
  ; archimedeanGammaTermDefined = λ f admissibleF → tt
  ; poleTermDefined = λ f admissibleF → tt
  ; trivialZeroTermDefined = λ f admissibleF → tt
  ; spectralZeroSumDefined = λ f admissibleF → tt
  ; sumIntegralInterchangesJustified = λ f admissibleF → tt
  }

toyComponentIdentity :
  ExplicitFormulaComponentIdentity toyWeilSpace toyComponents
toyComponentIdentity = record
  { arithmeticEqualsSpectral = λ f admissibleF → refl
  }

toyExplicitFormula : RiemannExplicitFormula toyWeilSpace
toyExplicitFormula =
  componentsToRiemannExplicitFormula
    toyWeilSpace toyComponents toyComponentIdentity

toyExplicitFormulaCloses :
  (f : Nat) →
  RiemannExplicitFormula.arithmeticForm toyExplicitFormula f
  ≡
  RiemannExplicitFormula.spectralZeroForm toyExplicitFormula f
toyExplicitFormulaCloses f =
  RiemannExplicitFormula.explicitFormula toyExplicitFormula f tt
