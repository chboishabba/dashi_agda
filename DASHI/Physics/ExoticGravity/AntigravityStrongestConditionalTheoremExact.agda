module DASHI.Physics.ExoticGravity.AntigravityStrongestConditionalTheoremExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.GR.GRWeakFieldPredictionReceipt as Weak
import DASHI.Physics.GR.SignedEinsteinCouplingBidiExact as Signed
import DASHI.Physics.GR.SignedNewtonianLimitBidiExact as Newton
import DASHI.Physics.GR.UniversalSignedGCrossScaleFingerprintBidiExact as Universal

import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti
import DASHI.Physics.ExoticGravity.AntigravityNegativeGCouplingBidiExact as NegativeG
import DASHI.Physics.ExoticGravity.AntigravityNegativeGCouplingScopeBidiExact as Scope
import DASHI.Physics.ExoticGravity.SuperconductingConstitutiveNegativeGScopeWeldExact as Constitutive
import DASHI.Physics.ExoticGravity.AntigravityCalibratedFullyDerivedExperimentalCutExact as Calibrated
import DASHI.Physics.ExoticGravity.AntigravityFullyDerivedExperimentalCutExact as FullyDerived
import DASHI.Physics.ExoticGravity.AntigravityExperimentalCutProvenanceExact as Provenance
import DASHI.Physics.ExoticGravity.AntigravityResearchPromotionCutExact as Promotion

------------------------------------------------------------------------
-- STRONGEST CURRENT ANTIGRAVITY THEOREM
--
-- This module deliberately separates three claims:
--
--   1. exact counterfactual mathematics:
--      a frozen negative Einstein/Newton coupling reverses every displayed
--      leading weak-field correction, and is not pointwise degenerate with the
--      ordinary positive-coupling fingerprint;
--
--   2. exact scope mathematics:
--      a material-effective negative coupling is a different hypothesis from
--      universal negative G;
--
--   3. conditional empirical promotion:
--      if the repo is supplied with both the typed constitutive negative-G
--      receipt and the calibrated fully-derived same-apparatus comparative
--      anomaly receipt for a remote repulsive field, the two may be carried
--      together as one maximally strong typed antigravity result.
--
-- No inhabitant of the empirical receipt is manufactured here.
------------------------------------------------------------------------

positiveGEveryDisplayedLeadingCorrection :
  (observable : Weak.GRWeakFieldObservable) →
  Signed.leadingCorrectionOrientation Signed.positiveCoupling observable
    ≡ Signed.conventionalCorrection
positiveGEveryDisplayedLeadingCorrection observable = refl

negativeGEveryDisplayedLeadingCorrection :
  (observable : Weak.GRWeakFieldObservable) →
  Signed.leadingCorrectionOrientation Signed.negativeCoupling observable
    ≡ Signed.reversedCorrection
negativeGEveryDisplayedLeadingCorrection =
  Signed.negativeGReversesEveryDisplayedLeadingCorrection

negativeAndPositiveLeadingCorrectionsSeparated :
  (observable : Weak.GRWeakFieldObservable) →
  Signed.leadingCorrectionOrientation Signed.negativeCoupling observable
    ≡ Signed.leadingCorrectionOrientation Signed.positiveCoupling observable →
  ⊥
negativeAndPositiveLeadingCorrectionsSeparated observable ()

negativeGNotPointwiseWeakFieldDegenerateWithPositiveG :
  ((observable : Weak.GRWeakFieldObservable) →
    Signed.leadingCorrectionOrientation Signed.negativeCoupling observable
      ≡ Signed.leadingCorrectionOrientation Signed.positiveCoupling observable) →
  ⊥
negativeGNotPointwiseWeakFieldDegenerateWithPositiveG pointwiseAgreement =
  negativeAndPositiveLeadingCorrectionsSeparated
    Weak.mercuryPerihelionAdvance
    (pointwiseAgreement Weak.mercuryPerihelionAdvance)

------------------------------------------------------------------------
-- The universal cross-scale fingerprints are already concrete in-repo.
-- Their local positive-density Newtonian responses point in opposite
-- directions, so a universal negative-G fingerprint cannot be observationally
-- identical even at this first local consumer.
------------------------------------------------------------------------

positiveUniversalGLocalResponse :
  Universal.localPositiveDensityResponse Universal.positiveGSignFingerprint
    ≡ Newton.attractiveTowardPositiveSource
positiveUniversalGLocalResponse = refl

negativeUniversalGLocalResponse :
  Universal.localPositiveDensityResponse Universal.negativeGSignFingerprint
    ≡ Newton.repulsiveAwayFromPositiveSource
negativeUniversalGLocalResponse = refl

universalPositiveAndNegativeGFingerprintsLocallySeparated :
  Universal.localPositiveDensityResponse Universal.negativeGSignFingerprint
    ≡ Universal.localPositiveDensityResponse Universal.positiveGSignFingerprint →
  ⊥
universalPositiveAndNegativeGFingerprintsLocallySeparated ()

------------------------------------------------------------------------
-- Local/material-effective negative G is not universal negative G.
------------------------------------------------------------------------

materialEffectiveScopeIsNotUniversal :
  Scope.materialEffectiveCoupling ≡ Scope.universalNewtonCoupling → ⊥
materialEffectiveScopeIsNotUniversal ()

universalScopeIsNotMaterialEffective :
  Scope.universalNewtonCoupling ≡ Scope.materialEffectiveCoupling → ⊥
universalScopeIsNotMaterialEffective ()

------------------------------------------------------------------------
-- Pull the terminal comparative-anomaly receipt out of the calibrated,
-- fully-derived provenance shell.
------------------------------------------------------------------------

terminalComparativeAnomaly :
  {claim : Anti.AntigravityClaim} →
  Calibrated.CalibratedFullyDerivedComparativeAnomalyReceipt claim →
  Promotion.ComparativeAnomalyReceipt claim
terminalComparativeAnomaly receipt =
  Provenance.anomaly
    (FullyDerived.provenancedAnomaly
      (Calibrated.anomaly receipt))

terminalComparativeStatus :
  {claim : Anti.AntigravityClaim} →
  Calibrated.CalibratedFullyDerivedComparativeAnomalyReceipt claim →
  Promotion.AntigravityResearchStatus
terminalComparativeStatus receipt =
  Promotion.statusFromComparativeAnomaly
    (terminalComparativeAnomaly receipt)

terminalComparativeStatusIsEstablished :
  {claim : Anti.AntigravityClaim} →
  (receipt : Calibrated.CalibratedFullyDerivedComparativeAnomalyReceipt claim) →
  terminalComparativeStatus receipt ≡ Promotion.comparativeAnomalyEstablished
terminalComparativeStatusIsEstablished receipt = refl

------------------------------------------------------------------------
-- MAXIMAL CONDITIONAL CONSTRUCTION
--
-- The remoteRepulsiveField claim is the strongest claim-specific target for
-- the current negative-coupling route: it binds an external-test-mass
-- discriminator, a material-effective constitutive sign reversal, a
-- calibrated/fully-derived same-apparatus comparative anomaly, and the exact
-- frozen/cross-scale sign consequences above.
------------------------------------------------------------------------

record MaximalRemoteRepulsiveAntigravityTheorem
    (constitutive : Constitutive.ConstitutiveNegativeGReceipt)
    (empirical :
      Calibrated.CalibratedFullyDerivedComparativeAnomalyReceipt
        Anti.remoteRepulsiveField) : Set₁ where
  constructor maximal-remote-repulsive-antigravity-theorem
  field
    claimProbe :
      NegativeG.NegativeGClaimProbe Anti.remoteRepulsiveField
    claimProbeIsCanonical :
      claimProbe ≡ NegativeG.remoteFieldNegativeGProbe

    fixedMeasuredSourceComparison :
      Constitutive.FixedMeasuredSourceComparison constitutive

    constitutiveSignMapping :
      Constitutive.ConstitutiveSignMapping constitutive

    candidateCouplingSign : Signed.CouplingSign
    candidateCouplingIsNegative :
      candidateCouplingSign ≡ Signed.negativeCoupling

    couplingScope : Scope.CouplingScope
    couplingScopeIsMaterialEffective :
      couplingScope ≡ Scope.materialEffectiveCoupling

    comparativeStatus : Promotion.AntigravityResearchStatus
    comparativeStatusIsEstablished :
      comparativeStatus ≡ Promotion.comparativeAnomalyEstablished

    everyDisplayedFrozenWeakFieldCorrectionReverses :
      (observable : Weak.GRWeakFieldObservable) →
      Signed.leadingCorrectionOrientation Signed.negativeCoupling observable
        ≡ Signed.reversedCorrection

    frozenNegativeGIsNotPointwisePositiveG :
      ((observable : Weak.GRWeakFieldObservable) →
        Signed.leadingCorrectionOrientation Signed.negativeCoupling observable
          ≡ Signed.leadingCorrectionOrientation Signed.positiveCoupling observable) →
      ⊥

    materialEffectiveScopeCannotBeUniversal :
      Scope.materialEffectiveCoupling ≡ Scope.universalNewtonCoupling → ⊥

    universalPositiveAndNegativeGFingerprintsDifferLocally :
      Universal.localPositiveDensityResponse Universal.negativeGSignFingerprint
        ≡ Universal.localPositiveDensityResponse Universal.positiveGSignFingerprint →
      ⊥

open MaximalRemoteRepulsiveAntigravityTheorem public

strongestCurrentRemoteRepulsiveAntigravityTheorem :
  (constitutive : Constitutive.ConstitutiveNegativeGReceipt) →
  (empirical :
    Calibrated.CalibratedFullyDerivedComparativeAnomalyReceipt
      Anti.remoteRepulsiveField) →
  MaximalRemoteRepulsiveAntigravityTheorem constitutive empirical
strongestCurrentRemoteRepulsiveAntigravityTheorem constitutive empirical =
  maximal-remote-repulsive-antigravity-theorem
    NegativeG.remoteFieldNegativeGProbe
    refl
    (Constitutive.fixedMeasuredSourceComparison constitutive)
    (Constitutive.constitutiveSignMapping constitutive)
    (Constitutive.candidateCoefficientSign constitutive)
    (Constitutive.candidateCoefficientIsNegative constitutive)
    (Constitutive.couplingScope constitutive)
    (Constitutive.couplingScopeIsMaterialEffective constitutive)
    (terminalComparativeStatus empirical)
    (terminalComparativeStatusIsEstablished empirical)
    negativeGEveryDisplayedLeadingCorrection
    negativeGNotPointwiseWeakFieldDegenerateWithPositiveG
    materialEffectiveScopeIsNotUniversal
    universalPositiveAndNegativeGFingerprintsLocallySeparated

------------------------------------------------------------------------
-- Promotion firewall.
--
-- The theorem above is intentionally conditional on explicit empirical and
-- constitutive receipts.  Its local/material-effective scope cannot be
-- rewritten into universal negative G, and the current empirical cut still
-- carries the repo's post-comparison residuals rather than a unique-mechanism
-- or universal-law promotion.
------------------------------------------------------------------------

record StrongestAntigravityBoundary : Set where
  constructor strongest-antigravity-boundary
  field
    negativeGFrozenWeakFieldFingerprintIsNontrivial : Bool
    negativeGIsPointwiseDegenerateWithPositiveG : Bool
    materialEffectiveNegativeGEqualsUniversalNegativeG : Bool
    calibratedFullyDerivedComparativeAnomalyRequired : Bool
    constitutiveNegativeGReceiptRequired : Bool
    theoremManufacturesMissingEmpiricalReceipt : Bool
    theoremPromotesUniversalNegativeG : Bool
    theoremPromotesUniqueMicroscopicMechanism : Bool

canonicalStrongestAntigravityBoundary : StrongestAntigravityBoundary
canonicalStrongestAntigravityBoundary =
  strongest-antigravity-boundary
    true false false true true false false false
