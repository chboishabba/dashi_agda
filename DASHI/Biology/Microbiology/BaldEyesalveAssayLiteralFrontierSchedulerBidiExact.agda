module DASHI.Biology.Microbiology.BaldEyesalveAssayLiteralFrontierSchedulerBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.LiteralFrontierSchedulerExact as Literal
import DASHI.Core.ProofSearchExperimentalParetoCrossPollinationExact as Cross
import DASHI.Chemistry.AssayDetectionEnvelopeExact as Assay
import DASHI.Chemistry.AssayParetoFrontierRefinementExact as AssayFrontier
import DASHI.Biology.Microbiology.BaldEyesalveRecursiveParetoFrontierBidiExact as Bald

------------------------------------------------------------------------
-- CHEMISTRY / BIOLOGY LITERAL FRONTIER SCHEDULER
--
-- These are experimental-science frontiers, so "close" means close the declared
-- experimental/consumer ambiguity, not manufacture a theorem or a clinical
-- efficacy claim.  Empirical evidence remains distinct from formal theorem
-- authority and from intervention permission.
------------------------------------------------------------------------

data AssayMove : Set where
  inferAbsenceFromNonDetect : AssayMove
  validateCalibrationCoordinate : AssayMove
  inspectMatrixEffect : AssayMove
  repeatUnchangedReadout : AssayMove


assayLiteralMove : AssayMove → Literal.LiteralFrontierMove
assayLiteralMove inferAbsenceFromNonDetect = Literal.literalFrontierMove
  Cross.physicalMeasurement
  "absence versus present-below-LOD collision"
  "promote non-detect directly to chemical absence"
  "noReliableSignal is observationally compatible with two distinct true states"
  "presence consumer"
  "same analyte/matrix/method"
  "method detection receipt required"
  "reject: nonfactorability witness"
assayLiteralMove validateCalibrationCoordinate = Literal.literalFrontierMove
  Cross.derivedExperimentalCoordinate
  "absence versus present-below-LOD collision"
  "validate calibrated concentration discriminator"
  "calibration may separate the current assay fibre"
  "presence/detection/quantification consumer"
  "same analyte x matrix x preparation x instrument"
  "calibration/derivation receipt required"
  "redirect: residual-relevant derived coordinate"
assayLiteralMove inspectMatrixEffect = Literal.literalFrontierMove
  Cross.physicalMeasurement
  "method detection envelope"
  "inspect matrix-effect coordinate"
  "matrix suppression/enhancement may explain reportable-surface collision"
  "assay adequacy consumer"
  "same analyte/matrix method family"
  "validated assay authority required"
  "redirect if matrix residual is live"
assayLiteralMove repeatUnchangedReadout = Literal.literalFrontierMove
  Cross.physicalMeasurement
  "absence versus present-below-LOD collision"
  "repeat unchanged coarse non-detect readout"
  "does not add a separating coordinate by construction"
  "presence consumer"
  "same coarse observation language"
  "measurement provenance only"
  "reject when no new resolution is introduced"

assayOutcome : (move : AssayMove) → Literal.LiteralMoveOutcome (assayLiteralMove move)
assayOutcome inferAbsenceFromNonDetect = Literal.rejected
  (Literal.rejectedLiteralMove Literal.knownNoGo
    "AssayDetectionEnvelopeExact proves non-detect cannot recover true absence"
    true refl)
assayOutcome validateCalibrationCoordinate = Literal.redirected
  (Literal.redirectedLiteralMove true refl
    "recompute presence/detection/quantification residual under a validated calibration"
    "original non-detect remains append-only evidence"
    "derived calibrated concentration is a discriminator, not a new physical dimension")
assayOutcome inspectMatrixEffect = Literal.redirected
  (Literal.redirectedLiteralMove true refl
    "recompute method envelope after matrix-effect characterization"
    "prior signal and extraction records remain retained"
    "matrix effect is a nuisance/systematic coordinate that may be residual-relevant")
assayOutcome repeatUnchangedReadout = Literal.rejected
  (Literal.rejectedLiteralMove Literal.residualIrrelevant
    "an unchanged coarse observation that does not split the live fibre is stale for this consumer"
    true refl)

assayPortfolio : Literal.LiteralFrontierPortfolio
assayPortfolio = Literal.literalFrontierPortfolio
  AssayMove assayLiteralMove assayOutcome
  "chemical presence/detection/quantification"
  "portfolio is scoped to the exact absence/sub-LOD collision and its immediate assay refinements"
  true refl

assayNonDetectCannotCloseAbsence : Assay.NonDetectImpliesAbsentPermission → ⊥
assayNonDetectCannotCloseAbsence = Assay.nonDetectCannotAutoPromoteToAbsent

------------------------------------------------------------------------
-- Bald's Eyesalve mechanism frontier.
------------------------------------------------------------------------

data BaldMove : Set where
  sulfurTrajectoryX1 : BaldMove
  thiolRecoveryX2X2F : BaldMove
  quorumAssociationX3 : BaldMove
  mediationX4 : BaldMove
  forceMixedMechanism : BaldMove
  repeatResolvedSulfurPanel : BaldMove


baldLiteralMove : BaldMove → Literal.LiteralFrontierMove
baldLiteralMove sulfurTrajectoryX1 = Literal.literalFrontierMove
  Cross.physicalMeasurement
  "fresh-to-day-9 sulfur trajectory"
  "BE-X1 time-resolved sulfur speciation"
  "target-preparation chemical trajectory unresolved"
  "mechanism-identification consumer"
  "same reconstructed preparation across time"
  "protocol/calibration receipt required"
  "redirect chemistry lane"
baldLiteralMove thiolRecoveryX2X2F = Literal.literalFrontierMove
  Cross.physicalMeasurement
  "thiol damage versus effective recovery"
  "BE-X2 plus BE-X2F matched thiol/recovery/function panel"
  "damage occupancy x recovery flux x functional restoration"
  "mechanism-identification consumer"
  "same preparation and organism"
  "protocol receipt required"
  "redirect recovery/function lane"
baldLiteralMove quorumAssociationX3 = Literal.literalFrontierMove
  Cross.physicalMeasurement
  "quorum-associated regulation"
  "BE-X3 quorum/virulence reporter panel"
  "association versus no association"
  "regulatory-association consumer"
  "same preparation/organism/exposure"
  "reporter protocol receipt required"
  "redirect only; reporter is not mediation"
baldLiteralMove mediationX4 = Literal.literalFrontierMove
  Cross.physicalMeasurement
  "association versus causal mediation"
  "BE-X4 branch-selective perturbation/rescue panel"
  "matched reporter/viability/biofilm response under admitted perturbation/rescue"
  "causal-mediation consumer"
  "same preparation/organism/phenotype context"
  "separate intervention authority + protocol receipt required"
  "redirect mediation lane"
baldLiteralMove forceMixedMechanism = Literal.literalFrontierMove
  Cross.symbolicProofRoute
  "unresolved mechanism frontier"
  "declare mixed mechanism without positive multi-lane evidence"
  "unresolved residual"
  "mechanism-identification consumer"
  "same target preparation"
  "positive multi-lane evidence missing"
  "reject: unresolved is not mixed"
baldLiteralMove repeatResolvedSulfurPanel = Literal.literalFrontierMove
  Cross.physicalMeasurement
  "downstream thiol/recovery/quorum/matrix collision"
  "repeat already-resolved BE-X1 sulfur panel"
  "historically valid chemistry evidence but no longer splits current live worlds"
  "mechanism-identification consumer"
  "same preparation"
  "measurement admissible but residual-irrelevant"
  "reject as stale for current live fibre"

baldOutcome : (move : BaldMove) → Literal.LiteralMoveOutcome (baldLiteralMove move)
baldOutcome sulfurTrajectoryX1 = Literal.redirected
  (Literal.redirectedLiteralMove true refl
    "resolve target-preparation sulfur trajectory before downstream mediation"
    "all previous phenotype/source evidence retained"
    "chemistry lane refinement")
baldOutcome thiolRecoveryX2X2F = Literal.redirected
  (Literal.redirectedLiteralMove true refl
    "separate damage-dominant from recovery-buffered worlds"
    "thiol modifications remain evidence even if dominance is revised"
    "recovery/function lane refinement")
baldOutcome quorumAssociationX3 = Literal.redirected
  (Literal.redirectedLiteralMove true refl
    "if association appears, open mediation rather than promote causality"
    "reporter result retained independently of later mediation outcome"
    "regulatory-association refinement")
baldOutcome mediationX4 = Literal.redirected
  (Literal.redirectedLiteralMove true refl
    "recompute causal-mediation residual from matched perturbation/rescue evidence"
    "association and phenotype evidence remain retained"
    "mediation refinement requires independent intervention authority")
baldOutcome forceMixedMechanism = Literal.rejected
  (Literal.rejectedLiteralMove Literal.authorityInsufficient
    "the recursive Bald frontier explicitly blocks unresolved -> mixed without positive multi-lane evidence"
    true refl)
baldOutcome repeatResolvedSulfurPanel = Literal.rejected
  (Literal.rejectedLiteralMove Literal.staleOrAlreadyOwned
    "resolved historical chemistry remains valid but should not be remeasured when it no longer splits the live mechanism fibre"
    true refl)

baldPortfolio : Literal.LiteralFrontierPortfolio
baldPortfolio = Literal.literalFrontierPortfolio
  BaldMove baldLiteralMove baldOutcome
  "Bald's Eyesalve mechanism-identification consumer"
  "X1/X2/X2F/X3/X4 are reused as the experiment vocabulary; only residual-relevant lanes are materialised"
  true refl

baldMixedFallbackStillBlocked :
  Bald.mixedMechanismIsFallbackForUnresolvedFrontier
    Bald.canonicalBaldEyesalveRecursiveParetoBoundary ≡ false
baldMixedFallbackStillBlocked =
  Bald.mixedMechanismIsFallbackForUnresolvedFrontierIsFalse
    Bald.canonicalBaldEyesalveRecursiveParetoBoundary

record BaldAssayLiteralFrontierBoundary : Set where
  constructor baldAssayLiteralFrontierBoundary
  field
    empiricalRedirectEqualsFormalTheoremClosure : Bool
    empiricalRedirectEqualsFormalTheoremClosureIsFalse :
      empiricalRedirectEqualsFormalTheoremClosure ≡ false
    staleExperimentMustBeRepeatedBecauseHistoricallyValid : Bool
    staleExperimentMustBeRepeatedBecauseHistoricallyValidIsFalse :
      staleExperimentMustBeRepeatedBecauseHistoricallyValid ≡ false
    unresolvedMechanismMayDefaultToMixed : Bool
    unresolvedMechanismMayDefaultToMixedIsFalse :
      unresolvedMechanismMayDefaultToMixed ≡ false
    residualRelevantExperimentCanOpenOneLaneOnly : Bool
    residualRelevantExperimentCanOpenOneLaneOnlyIsTrue :
      residualRelevantExperimentCanOpenOneLaneOnly ≡ true

canonicalBaldAssayLiteralFrontierBoundary : BaldAssayLiteralFrontierBoundary
canonicalBaldAssayLiteralFrontierBoundary =
  baldAssayLiteralFrontierBoundary false refl false refl false refl true refl
