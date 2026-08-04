module DASHI.Physics.YangMills.BalabanP33SandwichLocalFamilyExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators",
-- Springer Classics in Mathematics, 1995 reprint.
-- DOI: 10.1007/978-3-642-66282-9.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Turn one physically factorized operator channel E_c into the exact local
-- Hessian function
--
--   R_c(A,v) = <u_c,E_c(A)u_c> q_c(v),
--
-- where u_c is the normalized local direction and q_c(v) is its nonnegative
-- charge.  The existing three-stage operator-norm theorem gives the absolute
-- unit-form estimate; this module derives both signs, multiplies by q_c(v), and
-- constructs the finite signed family consumed by P33.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _≤_; ∣_∣; NonNegative)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4OperatorNormPipelineExact as Pipeline
import DASHI.Physics.YangMills.BalabanClayGate4SandwichOperatorToFormBoundExact as Sandwich
import DASHI.Physics.YangMills.BalabanP33FiveSandwichSignedFormExact as SignedForm
import DASHI.Physics.YangMills.BalabanP33PrimitiveOperatorNormLocalBoundsExact as Primitive
import DASHI.Physics.YangMills.BalabanP33LiteralFiveMechanismFamiliesExact as Literal
import DASHI.Physics.YangMills.BalabanP33FiniteSignedRemainderSummationExact as Signed
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums

record SandwichLocalFamilyData
    (Operator LocalState Background GlobalState Cell : Set) : Set₂ where
  field
    operatorAlgebra : Pipeline.OperatorNormAlgebra Operator ℚ
    formAlgebra : Sandwich.OperatorNormFormAlgebra
      Operator LocalState ℚ operatorAlgebra

    budget : Background → Cell →
      Sandwich.SandwichChannelNormBudget formAlgebra

    normalizedState : Background → GlobalState → Cell → LocalState
    normalizedStateIsUnit : ∀ background globalState cell →
      Sandwich.UnitState formAlgebra
        (normalizedState background globalState cell)

    coefficient : ℚ
    coefficientNonnegative : NonNegative coefficient

    radius : Background → GlobalState → ℚ
    radiusNonnegative : ∀ background globalState →
      0ℚ ≤ radius background globalState

    epsilonExact : ∀ background globalState cell →
      Sandwich.epsilon (budget background cell)
      ≡ coefficient * radius background globalState

    localCharge : Background → GlobalState → Cell → ℚ
    localChargeNonnegative : ∀ background globalState cell →
      0ℚ ≤ localCharge background globalState cell

    cells : Background → List Cell
    globalNormSq : Background → GlobalState → ℚ
    incidenceNormBound : ∀ background globalState →
      Sums.sumRational (cells background)
        (localCharge background globalState)
      ≤ globalNormSq background globalState

    orderMeaning :
      Pipeline.LessEqual operatorAlgebra ≡ _≤_
    absoluteMeaning : ∀ value →
      Sandwich.absolute formAlgebra value ≡ ∣ value ∣

open SandwichLocalFamilyData public

localUnitForm :
  ∀ {Operator LocalState Background GlobalState Cell} →
  SandwichLocalFamilyData
    Operator LocalState Background GlobalState Cell →
  Background → GlobalState → Cell → ℚ
localUnitForm dataSet background globalState cell =
  SignedForm.sandwichFormValue
    (budget dataSet background cell)
    (normalizedState dataSet background globalState cell)

localSandwichRemainder :
  ∀ {Operator LocalState Background GlobalState Cell} →
  SandwichLocalFamilyData
    Operator LocalState Background GlobalState Cell →
  Background → GlobalState → Cell → ℚ
localSandwichRemainder dataSet background globalState cell =
  localUnitForm dataSet background globalState cell
  * localCharge dataSet background globalState cell

localUnitFormConfiguredBound :
  ∀ {Operator LocalState Background GlobalState Cell}
    (dataSet : SandwichLocalFamilyData
      Operator LocalState Background GlobalState Cell)
    background globalState cell →
  Primitive.TwoSided
    (localUnitForm dataSet background globalState cell)
    (coefficient dataSet * radius dataSet background globalState)
localUnitFormConfiguredBound dataSet background globalState cell =
  SignedForm.configuredSandwichFormTwoSided
    (budget dataSet background cell)
    (normalizedState dataSet background globalState cell)
    (coefficient dataSet * radius dataSet background globalState)
    (orderMeaning dataSet)
    (absoluteMeaning dataSet)
    (normalizedStateIsUnit dataSet background globalState cell)
    (epsilonExact dataSet background globalState cell)

localSandwichRemainderBound :
  ∀ {Operator LocalState Background GlobalState Cell}
    (dataSet : SandwichLocalFamilyData
      Operator LocalState Background GlobalState Cell)
    background globalState cell →
  Primitive.TwoSided
    (localSandwichRemainder dataSet background globalState cell)
    (coefficient dataSet * radius dataSet background globalState
      * localCharge dataSet background globalState cell)
localSandwichRemainderBound dataSet background globalState cell =
  Literal.multiplyTwoSidedByNonnegative
    (localUnitForm dataSet background globalState cell)
    (coefficient dataSet * radius dataSet background globalState)
    (localCharge dataSet background globalState cell)
    (localUnitFormConfiguredBound dataSet background globalState cell)
    (localChargeNonnegative dataSet background globalState cell)

asFiniteSignedRemainderFamily :
  ∀ {Operator LocalState Background GlobalState Cell} →
  SandwichLocalFamilyData
    Operator LocalState Background GlobalState Cell →
  Signed.FiniteSignedRemainderFamily Background GlobalState Cell
asFiniteSignedRemainderFamily dataSet = record
  { Signed.FiniteSignedRemainderFamily.cells = cells dataSet
  ; Signed.FiniteSignedRemainderFamily.localRemainder =
      localSandwichRemainder dataSet
  ; Signed.FiniteSignedRemainderFamily.localNormCharge =
      localCharge dataSet
  ; Signed.FiniteSignedRemainderFamily.weight =
      λ background globalState →
        coefficient dataSet * radius dataSet background globalState
  ; Signed.FiniteSignedRemainderFamily.globalNormSq =
      globalNormSq dataSet
  ; Signed.FiniteSignedRemainderFamily.weightNonnegative =
      λ background globalState →
        let
          instance
            coefficientNN : NonNegative (coefficient dataSet)
            coefficientNN = coefficientNonnegative dataSet

            radiusNN : NonNegative (radius dataSet background globalState)
            radiusNN = ℚ.nonNegative
              (radiusNonnegative dataSet background globalState)

            productNN : NonNegative
              (coefficient dataSet * radius dataSet background globalState)
            productNN = ℚP.nonNeg*nonNeg⇒nonNeg
              (coefficient dataSet)
              (radius dataSet background globalState)
        in
        ℚP.nonNegative⁻¹
          (coefficient dataSet * radius dataSet background globalState)
  ; Signed.FiniteSignedRemainderFamily.pointwiseUpper =
      λ background globalState cell →
        Primitive.upper
          (localSandwichRemainderBound
            dataSet background globalState cell)
  ; Signed.FiniteSignedRemainderFamily.pointwiseLower =
      λ background globalState cell →
        Primitive.lower
          (localSandwichRemainderBound
            dataSet background globalState cell)
  ; Signed.FiniteSignedRemainderFamily.incidenceNormBound =
      incidenceNormBound dataSet
  }

sandwichLocalFunctionLevel : ProofLevel
sandwichLocalFunctionLevel = machineChecked

sandwichLocalSignedBoundLevel : ProofLevel
sandwichLocalSignedBoundLevel = machineChecked

sandwichLocalToFiniteFamilyLevel : ProofLevel
sandwichLocalToFiniteFamilyLevel = machineChecked
