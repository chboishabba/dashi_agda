module DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact where

------------------------------------------------------------------------
-- RH H_off^pole: NEAR/FAR BIDI DECOMPOSITION
--
-- Backward consumer:
--
--   B_off^pole + B_Gamma < M_cluster^pole.
--
-- Forward source already owned in the checked Lean cutoff return is stated
-- generically in the taper g:
--
--   |D_off(g,t,r) - 1/2 nearSignedSum(g,t,J)|
--     <= 1/2 C(g,r) farShellBound(A,|t|,J),
--
-- with farShellBound -> 0 as J -> infinity.
--
-- Therefore the final universal pole-quotient taper is an instantiation of the
-- same generic cutoff theorem; no extra analytic "same taper" theorem is made
-- into a research socket here.  This does NOT identify the separate rank-two
-- determinant taper q with the pole taper.
--
-- BIDI consequence: the infinite far shell is already controlled.  The first
-- unpaid H_off^pole theorem is the finite reflection-paired target-centred near
-- evaluation on the final high-ordinate pole taper.
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
-- Generic-family instantiation is not a new transport theorem.
------------------------------------------------------------------------

record TaperGenericBoundFamily : Set₁ where
  constructor taper-generic-bound-family
  field
    Taper Claim : Set
    boundAt : Taper → Claim

open TaperGenericBoundFamily public

instantiateGenericBoundAt :
  (family : TaperGenericBoundFamily) →
  (g : Taper family) →
  Claim family
instantiateGenericBoundAt family g = boundAt family g

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

    checkedLeanCutoffTheoremGenericInTaper : Bool
    checkedLeanCutoffTheoremGenericInTaperIsTrue :
      checkedLeanCutoffTheoremGenericInTaper ≡ true

    separatePoleTaperTransportResearchTheoremRequired : Bool
    separatePoleTaperTransportResearchTheoremRequiredIsFalse :
      separatePoleTaperTransportResearchTheoremRequired ≡ false

    reflectionPairOddChannelCancelled : Bool
    reflectionPairOddChannelCancelledIsTrue :
      reflectionPairOddChannelCancelled ≡ true

    arbitraryTargetSymmetryClosesNearCosineEvaluation : Bool
    arbitraryTargetSymmetryClosesNearCosineEvaluationIsFalse :
      arbitraryTargetSymmetryClosesNearCosineEvaluation ≡ false

    montgomeryVaughanDirectlyClosesNearCosineEvaluation : Bool
    montgomeryVaughanDirectlyClosesNearCosineEvaluationIsFalse :
      montgomeryVaughanDirectlyClosesNearCosineEvaluation ≡ false

    finitePoleQuotientNearSignedEvaluationClosed : Bool
    finitePoleQuotientNearSignedEvaluationClosedIsFalse :
      finitePoleQuotientNearSignedEvaluationClosed ≡ false

    infiniteFarTailIsPrimaryNewAnalyticObstruction : Bool
    infiniteFarTailIsPrimaryNewAnalyticObstructionIsFalse :
      infiniteFarTailIsPrimaryNewAnalyticObstruction ≡ false

    hOffPoleClosed : Bool
    hOffPoleClosedIsFalse : hOffPoleClosed ≡ false

    firstForwardLeaf : String
    postLeafCompiler : String
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
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "Evaluate the finite reflection-paired nearOffFinset cosine sum on the final high-ordinate pole-quotient taper, retaining target-centred phase, strongly enough that its near budget plus the explicit far-shell budget fits the remaining RH complement window."
    "Instantiate the already generic checked cutoff theorem at the pole taper, add the finite-near budget to the explicit far budget, then feed B_off^pole into B_off^pole + B_Gamma < M_cluster^pole."
    "The checked cutoff theorem is generic in its taper g, so final pole-taper instantiation is not promoted into a separate analytic research theorem. The rank-two determinant taper q remains a different carrier and is still not silently substituted. The infinite far shell and finite near carrier are already owned; H_off^pole is now concentrated on one finite signed target-centred near evaluation. Existing zeta symmetries and the bundled Montgomery-Vaughan owner do not directly close that evaluation. RH is not derived."

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
