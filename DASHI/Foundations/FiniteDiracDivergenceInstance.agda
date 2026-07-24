module DASHI.Foundations.FiniteDiracDivergenceInstance where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties using (≤-refl)

open import DASHI.Algebra.Quantum.TernaryCircuit using
  (QutritBasis; qNeg; qZero; qPos)
open import DASHI.Foundations.DivergenceComparisonPackage

------------------------------------------------------------------------
-- A concrete, exactly decidable finite instance.  Distributions are Dirac masses
-- on the three canonical qutrit outcomes.  TV, Hellinger², and JS are the discrete
-- 0/1 defect.  KL is defined only under absolute continuity (equal supports).

natDivergenceScalar : OrderedDivergenceScalar
natDivergenceScalar =
  record
    { Scalar = Nat
    ; zero = zero
    ; one = suc zero
    ; add = _+_
    ; mul = _*_
    ; LessEqual = _≤_
    }

data SameQutrit : QutritBasis → QutritBasis → Set where
  sameNeg : SameQutrit qNeg qNeg
  sameZero : SameQutrit qZero qZero
  samePos : SameQutrit qPos qPos

qutritDefect : QutritBasis → QutritBasis → Nat
qutritDefect qNeg qNeg = zero
qutritDefect qNeg qZero = suc zero
qutritDefect qNeg qPos = suc zero
qutritDefect qZero qNeg = suc zero
qutritDefect qZero qZero = zero
qutritDefect qZero qPos = suc zero
qutritDefect qPos qNeg = suc zero
qutritDefect qPos qZero = suc zero
qutritDefect qPos qPos = zero

qutritDefectSymmetric :
  ∀ x y →
  qutritDefect x y ≡ qutritDefect y x
qutritDefectSymmetric qNeg qNeg = refl
qutritDefectSymmetric qNeg qZero = refl
qutritDefectSymmetric qNeg qPos = refl
qutritDefectSymmetric qZero qNeg = refl
qutritDefectSymmetric qZero qZero = refl
qutritDefectSymmetric qZero qPos = refl
qutritDefectSymmetric qPos qNeg = refl
qutritDefectSymmetric qPos qZero = refl
qutritDefectSymmetric qPos qPos = refl

sameImpliesDefectZero :
  ∀ {x y} →
  SameQutrit x y →
  qutritDefect x y ≡ zero
sameImpliesDefectZero sameNeg = refl
sameImpliesDefectZero sameZero = refl
sameImpliesDefectZero samePos = refl

hellingerBelowTV-Dirac :
  ∀ x y →
  qutritDefect x y ≤ qutritDefect x y
hellingerBelowTV-Dirac x y = ≤-refl

tvSquaredBelowTwoHellinger-Dirac :
  ∀ x y →
  qutritDefect x y * qutritDefect x y
  ≤ (suc (suc zero)) * qutritDefect x y
tvSquaredBelowTwoHellinger-Dirac qNeg qNeg = ≤-refl
tvSquaredBelowTwoHellinger-Dirac qNeg qZero = ≤-refl
tvSquaredBelowTwoHellinger-Dirac qNeg qPos = ≤-refl
tvSquaredBelowTwoHellinger-Dirac qZero qNeg = ≤-refl
tvSquaredBelowTwoHellinger-Dirac qZero qZero = ≤-refl
tvSquaredBelowTwoHellinger-Dirac qZero qPos = ≤-refl
tvSquaredBelowTwoHellinger-Dirac qPos qNeg = ≤-refl
tvSquaredBelowTwoHellinger-Dirac qPos qZero = ≤-refl
tvSquaredBelowTwoHellinger-Dirac qPos qPos = ≤-refl

pinskerDirac :
  ∀ x y →
  SameQutrit x y →
  (suc (suc zero)) *
    (qutritDefect x y * qutritDefect x y)
  ≤ qutritDefect x y
pinskerDirac x y same
  rewrite sameImpliesDefectZero same = ≤-refl

finiteDiracDivergencePackage :
  DivergenceComparisonPackage QutritBasis natDivergenceScalar
finiteDiracDivergencePackage =
  record
    { TV = qutritDefect
    ; HellingerSq = qutritDefect
    ; KL = qutritDefect
    ; JS = qutritDefect
    ; AbsolutelyContinuous = SameQutrit
    ; DefinedKL = SameQutrit
    ; JSFinite = λ _ _ → SameQutrit qNeg qNeg
    ; klDomainImpliesAbsoluteContinuity = λ _ _ proof → proof
    ; hellingerSquaredBelowTV = hellingerBelowTV-Dirac
    ; tvSquaredBelowTwoHellingerSquared = tvSquaredBelowTwoHellinger-Dirac
    ; pinskerSquared = pinskerDirac
    ; jsFiniteWithoutSharedSupport = λ _ _ → sameNeg
    ; jsSymmetric = qutritDefectSymmetric
    }
