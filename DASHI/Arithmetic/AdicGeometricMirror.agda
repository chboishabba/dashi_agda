module DASHI.Arithmetic.AdicGeometricMirror where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Finite algebraic carrier for the n-adic geometric closure.
--
-- The analytic limit is deliberately separated from the exact partial-sum
-- recursion.  Prime bases may be interpreted in Q_p; composite bases use an
-- ideal-adic/product chart and are not promoted to new local fields.
------------------------------------------------------------------------

data CompletionKind : Set where
  primeFieldCompletion : CompletionKind
  compositeIdealCompletion : CompletionKind

geometricPartialSum : Nat → Nat → Nat
geometricPartialSum base zero = 1
geometricPartialSum base (suc depth) =
  1 + base * geometricPartialSum base depth

threePartial0 : geometricPartialSum 3 0 ≡ 1
threePartial0 = refl

threePartial1 : geometricPartialSum 3 1 ≡ 4
threePartial1 = refl

threePartial2 : geometricPartialSum 3 2 ≡ 13
threePartial2 = refl

threePartial3 : geometricPartialSum 3 3 ≡ 40
threePartial3 = refl

record AdicGeometricClosure : Set where
  constructor adic-geometric-closure
  field
    base : Nat
    mirrorDenominator : Nat
    denominatorSuccessorIsBase :
      mirrorDenominator + 1 ≡ base
    completionKind : CompletionKind
    formalClosureLabel : String
    finiteRecurrenceKernelChecked : Bool
    analyticCompletionImported : Bool
    standaloneCompositeFieldClaimed : Bool

canonicalThreeAdicClosure : AdicGeometricClosure
canonicalThreeAdicClosure = adic-geometric-closure
  3
  2
  refl
  primeFieldCompletion
  "1 + 3 + 3^2 + ... closes to -1/2 in the 3-adic completion"
  true
  false
  false

canonicalFourAdicIdealClosure : AdicGeometricClosure
canonicalFourAdicIdealClosure = adic-geometric-closure
  4
  3
  refl
  compositeIdealCompletion
  "1 + 4 + 4^2 + ... closes formally to -1/3 in the 4-adic ideal completion"
  true
  false
  false

canonicalTenAdicIdealClosure : AdicGeometricClosure
canonicalTenAdicIdealClosure = adic-geometric-closure
  10
  9
  refl
  compositeIdealCompletion
  "1 + 10 + 10^2 + ... closes formally to -1/9 in the 10-adic ideal completion"
  true
  false
  false

------------------------------------------------------------------------
-- Exact additive-mirror role for +1/2 and -1/2.
------------------------------------------------------------------------

data HalfPoint : Set where
  positiveHalf : HalfPoint
  zeroPoint : HalfPoint
  negativeHalf : HalfPoint

negateHalf : HalfPoint → HalfPoint
negateHalf positiveHalf = negativeHalf
negateHalf zeroPoint = zeroPoint
negateHalf negativeHalf = positiveHalf

combineHalf : HalfPoint → HalfPoint → HalfPoint
combineHalf positiveHalf negativeHalf = zeroPoint
combineHalf negativeHalf positiveHalf = zeroPoint
combineHalf zeroPoint y = y
combineHalf x zeroPoint = x
combineHalf positiveHalf positiveHalf = positiveHalf
combineHalf negativeHalf negativeHalf = negativeHalf

positiveNegativeCancel :
  combineHalf positiveHalf negativeHalf ≡ zeroPoint
positiveNegativeCancel = refl

negativePositiveCancel :
  combineHalf negativeHalf positiveHalf ≡ zeroPoint
negativePositiveCancel = refl

negationInvolutive : ∀ x → negateHalf (negateHalf x) ≡ x
negationInvolutive positiveHalf = refl
negationInvolutive zeroPoint = refl
negationInvolutive negativeHalf = refl

record HalfCompletionMirrorBridge : Set where
  field
    positiveBoundary : HalfPoint
    adicRemainder : HalfPoint
    additiveCancellation :
      combineHalf positiveBoundary adicRemainder ≡ zeroPoint
    geometricClosure : AdicGeometricClosure
    logisticCriticalCoordinateRole : Bool
    completionRolesDistinct : Bool
    topologicalIdentificationClaimed : Bool
    stage8IdentityClaimed : Bool

canonicalHalfCompletionMirrorBridge : HalfCompletionMirrorBridge
canonicalHalfCompletionMirrorBridge = record
  { positiveBoundary = positiveHalf
  ; adicRemainder = negativeHalf
  ; additiveCancellation = positiveNegativeCancel
  ; geometricClosure = canonicalThreeAdicClosure
  ; logisticCriticalCoordinateRole = true
  ; completionRolesDistinct = true
  ; topologicalIdentificationClaimed = false
  ; stage8IdentityClaimed = false
  }

record AdicMirrorAuthorityBoundary : Set where
  field
    generalFormulaRoleRecorded : Bool
    compositeCompletionPromotedToField : Bool
    finiteRecurrenceConfusedWithAnalyticLimit : Bool
    positiveHalfEqualsNegativeHalfClaimed : Bool
    stageSemanticsFollowFromArithmeticAlone : Bool

canonicalAdicMirrorAuthorityBoundary : AdicMirrorAuthorityBoundary
canonicalAdicMirrorAuthorityBoundary = record
  { generalFormulaRoleRecorded = true
  ; compositeCompletionPromotedToField = false
  ; finiteRecurrenceConfusedWithAnalyticLimit = false
  ; positiveHalfEqualsNegativeHalfClaimed = false
  ; stageSemanticsFollowFromArithmeticAlone = false
  }
