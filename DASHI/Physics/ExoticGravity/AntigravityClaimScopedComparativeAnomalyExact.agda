module DASHI.Physics.ExoticGravity.AntigravityClaimScopedComparativeAnomalyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti
import DASHI.Physics.ExoticGravity.AntigravityCalibratedFullyDerivedExperimentalCutExact as Calibrated
import DASHI.Physics.ExoticGravity.AntigravityClaimScopedExperimentalCutExact as Scoped
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- CLAIM-SCOPED CALIBRATION <-> COMPARATIVE ANOMALY SAME-OBJECT WELD
------------------------------------------------------------------------

record ClaimScopedComparativeAnomalyReceipt
    (claim : Anti.AntigravityClaim) : Set₁ where
  constructor claim-scoped-comparative-anomaly-receipt
  field
    scopedCut : Scoped.ClaimScopedCalibratedExperimentalCut claim
    anomaly : Calibrated.CalibratedFullyDerivedComparativeAnomalyReceipt claim
    sameCalibratedCut :
      Calibrated.experimentalCut anomaly
        ≡ Scoped.calibratedCut scopedCut

open ClaimScopedComparativeAnomalyReceipt public

------------------------------------------------------------------------
-- Reverse residuals.
------------------------------------------------------------------------

data ClaimScopedComparisonResidual : Set where
  missingClaimScopedCut : ClaimScopedComparisonResidual
  missingCalibratedComparativeAnomaly : ClaimScopedComparisonResidual
  missingSameCalibratedCutIdentity : ClaimScopedComparisonResidual

producerForClaimScopedComparisonResidual :
  ClaimScopedComparisonResidual → Search.ProducerClass
producerForClaimScopedComparisonResidual missingClaimScopedCut = Search.empiricalEvidenceProducer
producerForClaimScopedComparisonResidual missingCalibratedComparativeAnomaly = Search.discriminatorProducer
producerForClaimScopedComparisonResidual missingSameCalibratedCutIdentity = Search.identityProducer

data CurrentClaimScopedComparativeAuthority : Set where

noCurrentClaimScopedComparativeAnomaly :
  {claim : Anti.AntigravityClaim} →
  CurrentClaimScopedComparativeAuthority →
  ClaimScopedComparativeAnomalyReceipt claim
noCurrentClaimScopedComparativeAnomaly ()

record ClaimScopedComparisonBoundary : Set where
  constructor claim-scoped-comparison-boundary
  field
    sameClaimNameAloneWeldsExperimentalAndComparisonCuts : Bool
    exactCalibratedCutIdentityRequired : Bool
    consumerCalibrationMayBeDroppedAtComparison : Bool
    claimScopedComparativeAnomalyEqualsUniversalLaw : Bool

canonicalClaimScopedComparisonBoundary : ClaimScopedComparisonBoundary
canonicalClaimScopedComparisonBoundary =
  claim-scoped-comparison-boundary false true false false
