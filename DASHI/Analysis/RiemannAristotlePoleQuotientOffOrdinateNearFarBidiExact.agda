module DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact where

------------------------------------------------------------------------
-- RH H_off^pole: NEAR/FAR BIDI DECOMPOSITION
--
-- Backward consumer:
--
--   B_off^pole + B_Gamma < M_cluster^pole.
--
-- Forward source already owned in the checked Lean cutoff return:
--
--   |D_off - 1/2 nearSignedSum(t,J)|
--     <= 1/2 C farShellBound(A,|t|,J),
--
-- with farShellBound -> 0 as J -> infinity.
--
-- The important carrier boundary is that this older cutoff theorem may only be
-- reused for the final universal pole quotient after a literal same-taper /
-- same-response transport is supplied.  The checked rank-two determinant taper
-- q is not silently substituted here.
--
-- Once the carrier transport is available, H_off^pole is reduced to a finite
-- signed near evaluation plus the already-controlled far remainder.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotleExplicitCutoffCarrierLeanReturnExact as Cutoff
import DASHI.Analysis.RiemannAristotleReflectionPairKernelReturnExact as Reflection
import DASHI.Analysis.RiemannAristotleG2eTargetCenteredSymmetryNoGoExact as SymmetryNoGo

------------------------------------------------------------------------
-- Generic ordered-additive compiler.
------------------------------------------------------------------------

record OrderedAdditiveNearFarSurface : Set₁ where
  constructor ordered-additive-near-far-surface
  field
    Scalar : Set
    _≤_ : Scalar → Scalar → Set
    add : Scalar → Scalar → Scalar
    ≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
    addMonotone : ∀ {a a' b b'} → a ≤ a' → b ≤ b' → add a b ≤ add a' b'

open OrderedAdditiveNearFarSurface public

record NearFarOffOrdinateBudget
    (S : OrderedAdditiveNearFarSurface) : Set where
  constructor near-far-off-ordinate-budget
  field
    fullResponse nearResponse farRemainder : Scalar S
    nearBudget farBudget : Scalar S

    fullBelowNearPlusFar :
      _≤_ S fullResponse (add S nearResponse farRemainder)

    nearUpper : _≤_ S nearResponse nearBudget
    farUpper : _≤_ S farRemainder farBudget

open NearFarOffOrdinateBudget public

compiledOffOrdinateUpper :
  (S : OrderedAdditiveNearFarSurface) →
  (d : NearFarOffOrdinateBudget S) →
  _≤_ S
    (fullResponse d)
    (add S (nearBudget d) (farBudget d))
compiledOffOrdinateUpper S d =
  ≤-trans S
    (fullBelowNearPlusFar d)
    (addMonotone S (nearUpper d) (farUpper d))

------------------------------------------------------------------------
-- Carrier transport gate.
--
-- This is intentionally stronger than matching names.  The application must
-- identify the taper and the response consumed by the old cutoff theorem with
-- the taper and off-ordinate response used by the final pole-quotient consumer.
------------------------------------------------------------------------

record PoleCutoffCarrierTransport : Set₁ where
  constructor pole-cutoff-carrier-transport
  field
    Taper Response : Set
    cutoffTaper poleQuotientTaper : Taper
    cutoffResponse poleQuotientResponse : Taper → Response

    sameTaper : cutoffTaper ≡ poleQuotientTaper
    sameResponse :
      (g : Taper) → cutoffResponse g ≡ poleQuotientResponse g

    transportReference : String

open PoleCutoffCarrierTransport public

------------------------------------------------------------------------
-- Exact source/frontier audit.
------------------------------------------------------------------------

record PoleQuotientOffOrdinateNearFarBoundary : Set where
  constructor pole-quotient-off-ordinate-near-far-boundary
  field
    checkedLeanFarShellBoundOwned : Bool
    checkedLeanFarShellBoundOwnedIsTrue : checkedLeanFarShellBoundOwned ≡ true

    checkedLeanFarShellTendsToZeroOwned : Bool
    checkedLeanFarShellTendsToZeroOwnedIsTrue :
      checkedLeanFarShellTendsToZeroOwned ≡ true

    checkedLeanFiniteNearCarrierOwned : Bool
    checkedLeanFiniteNearCarrierOwnedIsTrue : checkedLeanFiniteNearCarrierOwned ≡ true

    reflectionPairOddChannelCancelled : Bool
    reflectionPairOddChannelCancelledIsTrue :
      reflectionPairOddChannelCancelled ≡ true

    arbitraryTargetSymmetryClosesNearCosineEvaluation : Bool
    arbitraryTargetSymmetryClosesNearCosineEvaluationIsFalse :
      arbitraryTargetSymmetryClosesNearCosineEvaluation ≡ false

    montgomeryVaughanDirectlyClosesNearCosineEvaluation : Bool
    montgomeryVaughanDirectlyClosesNearCosineEvaluationIsFalse :
      montgomeryVaughanDirectlyClosesNearCosineEvaluation ≡ false

    oldCutoffCarrierTransportedToFinalPoleQuotientCarrier : Bool
    oldCutoffCarrierTransportedToFinalPoleQuotientCarrierIsFalse :
      oldCutoffCarrierTransportedToFinalPoleQuotientCarrier ≡ false

    finitePoleQuotientNearSignedEvaluationClosed : Bool
    finitePoleQuotientNearSignedEvaluationClosedIsFalse :
      finitePoleQuotientNearSignedEvaluationClosed ≡ false

    infiniteFarTailIsPrimaryNewAnalyticObstruction : Bool
    infiniteFarTailIsPrimaryNewAnalyticObstructionIsFalse :
      infiniteFarTailIsPrimaryNewAnalyticObstruction ≡ false

    hOffPoleClosed : Bool
    hOffPoleClosedIsFalse : hOffPoleClosed ≡ false

    firstForwardLeaf : String
    secondForwardLeaf : String
    boundedReading : String

canonicalPoleQuotientOffOrdinateNearFarBoundary :
  PoleQuotientOffOrdinateNearFarBoundary
canonicalPoleQuotientOffOrdinateNearFarBoundary =
  pole-quotient-off-ordinate-near-far-boundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "Prove a literal same-taper/same-response transport from the checked OffOrdinateCutoffCarrier theorem to the universal pole-quotient taper used by the final RH consumer."
    "On that transported carrier, evaluate the finite reflection-paired nearOffFinset cosine sum with target-centred phase strongly enough that nearBudget + explicitFarBudget fits the remaining RH complement window."
    "The checked 8883 Lean return already owns arbitrary-accuracy control of the infinite far shell and the finite near carrier. Reflection pairing already removes the odd sinh*sin channel. Therefore H_off^pole should not be attacked as a fresh infinite absolute-tail problem. Its exact remaining forward work is carrier transport plus finite signed target-centred near evaluation. Existing zeta symmetries and the bundled Montgomery-Vaughan owner do not directly supply that local cosine evaluation. RH is not derived."

------------------------------------------------------------------------
-- Regression against the cited source owners.
------------------------------------------------------------------------

cutoffFarTailOwnedInLean :
  Cutoff.explicitFarShellFormulaOwned Cutoff.canonicalExplicitCutoffCarrierLeanReturn
  ≡ true
cutoffFarTailOwnedInLean = refl

cutoffFiniteNearCarrierOwnedInLean :
  Cutoff.finiteSignedNearCarrierOwned Cutoff.canonicalExplicitCutoffCarrierLeanReturn
  ≡ true
cutoffFiniteNearCarrierOwnedInLean = refl

reflectionOddChannelAlreadyCancelled :
  Reflection.reflectionPairOddTermCancelledExactly
    Reflection.canonicalReflectionPairKernelReturn ≡ true
reflectionOddChannelAlreadyCancelled = refl

existingSymmetryDoesNotCloseTargetCentredCancellation :
  SymmetryNoGo.targetCenteredScalarCancellationClosed
    SymmetryNoGo.canonicalG2eTargetCenteredSymmetryNoGo ≡ false
existingSymmetryDoesNotCloseTargetCentredCancellation = refl
