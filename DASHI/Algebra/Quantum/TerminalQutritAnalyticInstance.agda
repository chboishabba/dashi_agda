module DASHI.Algebra.Quantum.TerminalQutritAnalyticInstance where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Analysis.ConstructiveRealSpine
open import DASHI.Analysis.ConcreteComplex
open import DASHI.Analysis.TerminalConstructedAnalyticModel
open import DASHI.Algebra.Quantum.QutritAmplitude
open import DASHI.Algebra.Quantum.ConcreteQutritScalar

terminalComplexStarSemiringLaws :
  ComplexPairStarSemiringLaws terminalReal
terminalComplexStarSemiringLaws =
  record
    { addZeroLeftC = λ { (complex tt tt) → refl }
    ; addZeroRightC = λ { (complex tt tt) → refl }
    ; mulOneLeftC = λ { (complex tt tt) → refl }
    ; mulOneRightC = λ { (complex tt tt) → refl }
    ; conjugateInvolutiveLaw = λ { (complex tt tt) → refl }
    }

terminalQutritScalarPackage : ConcreteQutritScalarPackage
terminalQutritScalarPackage =
  record
    { real = terminalReal
    ; complexLaws = terminalComplexStarSemiringLaws
    }

terminalQutritBornPackage :
  ConcreteQutritBornPackage terminalQutritScalarPackage
terminalQutritBornPackage =
  record
    { NonnegativeReal = ⊤
    ; fromNormSquare = λ _ → tt
    ; probabilityOne = tt
    ; addProbability = λ _ _ → tt
    ; bornNormalization = λ _ _ → refl
    }

terminalBornAuthority :
  QutritBornAuthority (scalarSemiring terminalQutritScalarPackage)
terminalBornAuthority =
  record
    { Probability = ⊤
    ; probabilityOfScalar = λ _ → tt
    ; totalOne = tt
    ; _+P_ = λ _ _ → tt
    ; bornTotal = λ _ _ → refl
    }

terminalBasisMeasurement :
  ∀ q →
  QutritMeasurement
    terminalBornAuthority
    (basisState (scalarSemiring terminalQutritScalarPackage) q)
terminalBasisMeasurement q =
  record
    { normalized = basisNormalized q }
  where
    basisNormalized :
      ∀ q →
      Normalized
        (basisState (scalarSemiring terminalQutritScalarPackage) q)
    basisNormalized q = refl
