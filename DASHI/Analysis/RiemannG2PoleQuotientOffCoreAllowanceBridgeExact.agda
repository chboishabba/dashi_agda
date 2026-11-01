module DASHI.Analysis.RiemannG2PoleQuotientOffCoreAllowanceBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.TwoChannelAllowanceCompositionExact as Core
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2PoleQuotientOffIntermediateAllowanceCompilerExact as Off

------------------------------------------------------------------------
-- RIEMANN FINAL OFF IS AN INSTANCE OF THE GENERIC TWO-CHANNEL COMPILER
--
-- Keep the existing Riemann record/API, but make its order/addition theorem an
-- explicit instance of the domain-neutral Core owner.
------------------------------------------------------------------------

coreSurfaceFromNearFar :
  NearFar.OrderedAdditiveNearFarSurface ->
  Core.OrderedAdditiveTwoChannelSurface
coreSurfaceFromNearFar S =
  Core.ordered-additive-two-channel-surface
    (NearFar.Scalar S)
    (NearFar._≤_ S)
    (NearFar.add S)
    (NearFar.≤-trans S)
    (NearFar.addMonotone S)

coreFitFromRiemann :
  (S : NearFar.OrderedAdditiveNearFarSurface) ->
  (d : NearFar.NearFarOffOrdinateBudget S) ->
  (assigned : NearFar.Scalar S) ->
  Off.IntermediateNearFarAllowanceFit S d assigned ->
  Core.IntermediateAllowanceFit
    (coreSurfaceFromNearFar S)
    (NearFar.nearBudget d)
    (NearFar.farBudget d)
    assigned
coreFitFromRiemann S d assigned fit =
  Core.intermediate-allowance-fit
    (Off.intermediateFarAllowance fit)
    (Off.nearBudgetSelfOrder fit)
    (Off.farBudgetBelowIntermediateAllowance fit)
    (Off.nearBudgetPlusIntermediateBelowAssigned fit)

compiledNearPlusFarBelowAssignedViaCore :
  (S : NearFar.OrderedAdditiveNearFarSurface) ->
  (d : NearFar.NearFarOffOrdinateBudget S) ->
  (assigned : NearFar.Scalar S) ->
  Off.IntermediateNearFarAllowanceFit S d assigned ->
  NearFar._≤_ S
    (NearFar.add S
      (NearFar.nearBudget d)
      (NearFar.farBudget d))
    assigned
compiledNearPlusFarBelowAssignedViaCore S d assigned fit =
  Core.combinedEnvelopeBelowAssigned
    (coreSurfaceFromNearFar S)
    (NearFar.nearBudget d)
    (NearFar.farBudget d)
    assigned
    (coreFitFromRiemann S d assigned fit)

------------------------------------------------------------------------
-- Cross-domain calibration: the old rational Riemann and NS two-channel
-- compositions are specializations of this same Core proof shape.  This module
-- transfers no physical or analytic source authority between those domains.
------------------------------------------------------------------------

record RiemannOffCoreAllowanceBoundary : Set where
  constructor riemann-off-core-allowance-boundary
  field
    riemannOffUsesGenericTwoChannelComposition : Bool
    riemannOffUsesGenericTwoChannelCompositionIsTrue :
      riemannOffUsesGenericTwoChannelComposition ≡ true

    rHSpecificAlgebraTheoremNeeded : Bool
    rHSpecificAlgebraTheoremNeededIsFalse :
      rHSpecificAlgebraTheoremNeeded ≡ false

    nsPhysicalEstimateImportedIntoRiemann : Bool
    nsPhysicalEstimateImportedIntoRiemannIsFalse :
      nsPhysicalEstimateImportedIntoRiemann ≡ false

    channelEstimatesRemainDomainSpecific : Bool
    channelEstimatesRemainDomainSpecificIsTrue :
      channelEstimatesRemainDomainSpecific ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    boundedReading : String

canonicalRiemannOffCoreAllowanceBoundary : RiemannOffCoreAllowanceBoundary
canonicalRiemannOffCoreAllowanceBoundary =
  riemann-off-core-allowance-boundary
    true refl
    false refl
    false refl
    true refl
    false refl
    "The final Riemann Off near/far allowance composition is an instance of the generic Core two-channel theorem. Only the order/addition proof shape is shared with other domains such as the NS terminal far/near budget. The actual Riemann finite-near estimate, far-tail estimate, cutoff identity and assigned allowance remain Riemann-specific. No NS estimate or source authority is transported, and RH is not derived."
