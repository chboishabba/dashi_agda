module DASHI.Physics.Closure.NSNegativeSobolevDangerShellReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSTailFluxLPIdentityFullDerivationReceipt as Full
import DASHI.Physics.Closure.NSDangerShellMaximumPrincipleReceipt as Danger
import DASHI.Physics.Closure.NSPressureVsDepthLPClarificationReceipt
  as PressureDepth

------------------------------------------------------------------------
-- Negative-Sobolev danger-shell target.
--
-- This receipt records the corrected non-circular high-high target:
-- do not assume H^{1/2}, Serrin, BKM, or stronger regularity of the
-- velocity.  Instead, place the nonlinear defect
--
--   P_{>K*}(u . grad u)
--
-- in H^{-1/2} and pair it against the tail velocity in H^{1/2}.  The
-- load-bearing analytic estimate is the open bound
--
--   || P_{>K*}(u . grad u) ||_{H^{-1/2}}
--     <= epsilon * nu * || P_{>K*} u ||_{H^{3/2}}.
--
-- If that estimate is proved without importing regularity, the dual
-- pairing and tail interpolation feed the theta/danger-shell barrier.
-- This module does not prove that estimate and does not promote Clay NS.

data NSNegativeSobolevStatus : Set where
  hMinusHalfDangerShellTargetRecorded :
    NSNegativeSobolevStatus

data NegativeSobolevFluxStep : Set where
  nonlinearDefectLivesInHMinusHalfTarget :
    NegativeSobolevFluxStep

  dualPairingHMinusHalfWithHPlusHalf :
    NegativeSobolevFluxStep

  highHighDefectBoundAtDangerShell :
    NegativeSobolevFluxStep

  tailInterpolationHPlusHalfToHThreeHalf :
    NegativeSobolevFluxStep

  interpolationAbsorbsFluxIntoDissipation :
    NegativeSobolevFluxStep

  epsilonPlusThetaBelowOneGivesBarrier :
    NegativeSobolevFluxStep

canonicalNegativeSobolevFluxSteps :
  List NegativeSobolevFluxStep
canonicalNegativeSobolevFluxSteps =
  nonlinearDefectLivesInHMinusHalfTarget
  ∷ dualPairingHMinusHalfWithHPlusHalf
  ∷ highHighDefectBoundAtDangerShell
  ∷ tailInterpolationHPlusHalfToHThreeHalf
  ∷ interpolationAbsorbsFluxIntoDissipation
  ∷ epsilonPlusThetaBelowOneGivesBarrier
  ∷ []

data NegativeSobolevOpenObligation : Set where
  proveNonlinearDefectHMinusHalfBound :
    NegativeSobolevOpenObligation

  proveBoundWithoutHOneHalfVelocityInput :
    NegativeSobolevOpenObligation

  proveBoundWithoutSerrinOrBKMInput :
    NegativeSobolevOpenObligation

  proveTailInterpolationMatchesEV5DissipationWeights :
    NegativeSobolevOpenObligation

  combineWithKStarDriftContainment :
    NegativeSobolevOpenObligation

canonicalNegativeSobolevOpenObligations :
  List NegativeSobolevOpenObligation
canonicalNegativeSobolevOpenObligations =
  proveNonlinearDefectHMinusHalfBound
  ∷ proveBoundWithoutHOneHalfVelocityInput
  ∷ proveBoundWithoutSerrinOrBKMInput
  ∷ proveTailInterpolationMatchesEV5DissipationWeights
  ∷ combineWithKStarDriftContainment
  ∷ []

data ForbiddenNegativeSobolevShortcut : Set where
  importingHOneHalfVelocityRegularity :
    ForbiddenNegativeSobolevShortcut

  importingSerrinContinuation :
    ForbiddenNegativeSobolevShortcut

  importingBKMContinuation :
    ForbiddenNegativeSobolevShortcut

  treatingDualEstimateAsAlreadyProved :
    ForbiddenNegativeSobolevShortcut

canonicalForbiddenNegativeSobolevShortcuts :
  List ForbiddenNegativeSobolevShortcut
canonicalForbiddenNegativeSobolevShortcuts =
  importingHOneHalfVelocityRegularity
  ∷ importingSerrinContinuation
  ∷ importingBKMContinuation
  ∷ treatingDualEstimateAsAlreadyProved
  ∷ []

data NSNegativeSobolevPromotion : Set where

nsNegativeSobolevPromotionImpossibleHere :
  NSNegativeSobolevPromotion →
  ⊥
nsNegativeSobolevPromotionImpossibleHere ()

negativeSobolevTargetFormula :
  String
negativeSobolevTargetFormula =
  "Target: ||P_{>K*}(u.grad u)||_{H^{-1/2}} <= epsilon*nu*||P_{>K*}u||_{H^{3/2}}; dual pairing with P_{>K*}u in H^{1/2} then absorbs high-high flux into dissipation when epsilon+theta<1."

negativeSobolevBoundaryText :
  String
negativeSobolevBoundaryText =
  "This is a theorem target, not a proof.  It replaces the circular H^{1/2} velocity-control route with a negative-Sobolev nonlinear-defect estimate.  The estimate must be proved without H^{1/2}, Serrin, BKM, or stronger regularity inputs."

record NSNegativeSobolevDangerShellReceipt (K : Nat) : Setω where
  field
    status :
      NSNegativeSobolevStatus

    statusIsCanonical :
      status ≡ hMinusHalfDangerShellTargetRecorded

    fullIdentityReceipt :
      Full.NSTailFluxLPIdentityFullDerivationReceipt K

    fullIdentityDerived :
      Full.lpIdentityDerivedHere fullIdentityReceipt ≡ true

    fullIdentityNoThetaProof :
      Full.thetaLessThanOneProvedHere fullIdentityReceipt ≡ false

    fullIdentityNoClay :
      Full.clayNavierStokesPromoted fullIdentityReceipt ≡ false

    pressureDepthReceipt :
      PressureDepth.NSPressureVsDepthLPClarificationReceipt

    pressureDangerShellTarget :
      PressureDepth.dangerShellMaxPrincipleTargetClarified
        pressureDepthReceipt
      ≡
      true

    pressureDepthNoClay :
      PressureDepth.clayNavierStokesPromoted pressureDepthReceipt ≡ false

    dangerShellReceipt :
      Danger.NSDangerShellMaximumPrincipleReceipt

    dangerShellStillOpen :
      Danger.dangerShellMaxPrincipleProved dangerShellReceipt ≡ false

    fluxSteps :
      List NegativeSobolevFluxStep

    fluxStepsAreCanonical :
      fluxSteps ≡ canonicalNegativeSobolevFluxSteps

    openObligations :
      List NegativeSobolevOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalNegativeSobolevOpenObligations

    forbiddenShortcuts :
      List ForbiddenNegativeSobolevShortcut

    forbiddenShortcutsAreCanonical :
      forbiddenShortcuts ≡ canonicalForbiddenNegativeSobolevShortcuts

    formula :
      String

    formulaIsCanonical :
      formula ≡ negativeSobolevTargetFormula

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ negativeSobolevBoundaryText

    nonlinearDefectSpaceTargetRecorded :
      Bool

    nonlinearDefectSpaceTargetRecordedIsTrue :
      nonlinearDefectSpaceTargetRecorded ≡ true

    dualPairingRecorded :
      Bool

    dualPairingRecordedIsTrue :
      dualPairingRecorded ≡ true

    highHighDefectBoundProvedHere :
      Bool

    highHighDefectBoundProvedHereIsFalse :
      highHighDefectBoundProvedHere ≡ false

    interpolationAbsorptionProvedHere :
      Bool

    interpolationAbsorptionProvedHereIsFalse :
      interpolationAbsorptionProvedHere ≡ false

    hOneHalfVelocityRegularityAssumed :
      Bool

    hOneHalfVelocityRegularityAssumedIsFalse :
      hOneHalfVelocityRegularityAssumed ≡ false

    serrinOrBKMAssumed :
      Bool

    serrinOrBKMAssumedIsFalse :
      serrinOrBKMAssumed ≡ false

    dangerShellBarrierProvedHere :
      Bool

    dangerShellBarrierProvedHereIsFalse :
      dangerShellBarrierProvedHere ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotions :
      List NSNegativeSobolevPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      NSNegativeSobolevPromotion →
      ⊥

open NSNegativeSobolevDangerShellReceipt public

canonicalNSNegativeSobolevDangerShellReceipt :
  NSNegativeSobolevDangerShellReceipt zero
canonicalNSNegativeSobolevDangerShellReceipt =
  record
    { status =
        hMinusHalfDangerShellTargetRecorded
    ; statusIsCanonical =
        refl
    ; fullIdentityReceipt =
        Full.canonicalNSTailFluxLPIdentityFullDerivationReceipt
    ; fullIdentityDerived =
        refl
    ; fullIdentityNoThetaProof =
        refl
    ; fullIdentityNoClay =
        refl
    ; pressureDepthReceipt =
        PressureDepth.canonicalNSPressureVsDepthLPClarificationReceipt
    ; pressureDangerShellTarget =
        refl
    ; pressureDepthNoClay =
        refl
    ; dangerShellReceipt =
        Danger.canonicalNSDangerShellMaximumPrincipleReceipt
    ; dangerShellStillOpen =
        refl
    ; fluxSteps =
        canonicalNegativeSobolevFluxSteps
    ; fluxStepsAreCanonical =
        refl
    ; openObligations =
        canonicalNegativeSobolevOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; forbiddenShortcuts =
        canonicalForbiddenNegativeSobolevShortcuts
    ; forbiddenShortcutsAreCanonical =
        refl
    ; formula =
        negativeSobolevTargetFormula
    ; formulaIsCanonical =
        refl
    ; boundary =
        negativeSobolevBoundaryText
    ; boundaryIsCanonical =
        refl
    ; nonlinearDefectSpaceTargetRecorded =
        true
    ; nonlinearDefectSpaceTargetRecordedIsTrue =
        refl
    ; dualPairingRecorded =
        true
    ; dualPairingRecordedIsTrue =
        refl
    ; highHighDefectBoundProvedHere =
        false
    ; highHighDefectBoundProvedHereIsFalse =
        refl
    ; interpolationAbsorptionProvedHere =
        false
    ; interpolationAbsorptionProvedHereIsFalse =
        refl
    ; hOneHalfVelocityRegularityAssumed =
        false
    ; hOneHalfVelocityRegularityAssumedIsFalse =
        refl
    ; serrinOrBKMAssumed =
        false
    ; serrinOrBKMAssumedIsFalse =
        refl
    ; dangerShellBarrierProvedHere =
        false
    ; dangerShellBarrierProvedHereIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        nsNegativeSobolevPromotionImpossibleHere
    }

canonicalNSNegativeSobolevTargetRecorded :
  nonlinearDefectSpaceTargetRecorded
    canonicalNSNegativeSobolevDangerShellReceipt
  ≡
  true
canonicalNSNegativeSobolevTargetRecorded =
  refl

canonicalNSNegativeSobolevNoClayPromotion :
  clayNavierStokesPromoted canonicalNSNegativeSobolevDangerShellReceipt
  ≡
  false
canonicalNSNegativeSobolevNoClayPromotion =
  refl
