module DASHI.Culture.JohnAnthonyBrownSelectiveInvalidationParetoBidiExact where

open import DASHI.Core.Prelude

import DASHI.Culture.JohnAnthonyBrownDiagnosisRepairSchedulerBidiExact as Diagnosis
import DASHI.Culture.JohnAnthonyBrownTemporalDiagnosisDependencyLineageBidiExact as Lineage
import DASHI.Culture.JohnAnthonyBrownReceptionEvidenceReopeningBridgeExact as Brown
import DASHI.Core.AffectedDependencyClosureExact as Closure
import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Outcome
import DASHI.Core.SequentialOutcomeBackpropagationBidiExact as Revision
import DASHI.Core.SelectiveInvalidationParetoFrontierBidiExact as Pareto

------------------------------------------------------------------------
-- JOHN ANTHONY BROWN SELECTIVE INVALIDATION / PARETO RETURN
------------------------------------------------------------------------

h1OutcomeMeasurementCertificate : Pareto.CertificateCandidate
h1OutcomeMeasurementCertificate =
  Pareto.certificate-candidate
    "outcome measurement -> H1 association claim"
    Outcome.observationConflict
    Pareto.mustRecompute
    0 0 0 2
    "later outcome-measurement event is the exact H1 reactivation path"

h1ExposureMeasurementCertificate : Pareto.CertificateCandidate
h1ExposureMeasurementCertificate =
  Pareto.certificate-candidate
    "exposure measurement -> H1 association claim"
    Outcome.observationConflict
    Pareto.provablyUnaffected
    4 4 0 0
    "earlier exposure-path audit remains retained; later outcome reactivation does not retroactively invalidate it"

h5ConfoundingCertificate : Pareto.CertificateCandidate
h5ConfoundingCertificate =
  Pareto.certificate-candidate
    "confounding model -> H5 adjusted association"
    Outcome.modelConflict
    Pareto.provablyUnaffected
    4 3 0 0
    "different H5 consumer and upstream path remain outside current H1 frontier"

h1ConsumerReview : Pareto.CertificateCandidate
h1ConsumerReview =
  Pareto.certificate-candidate
    "H1 interpretation/consumer review"
    Outcome.consumerMismatch
    Pareto.mayRecompute
    2 1 0 1
    "review only if recomputed H1 measurement support changes the declared consumer answer"

rightsPolicyAuthority : Pareto.CertificateCandidate
rightsPolicyAuthority =
  Pareto.certificate-candidate
    "rights/policy authority surface"
    Outcome.authorityMismatch
    Pareto.authorityBlocked
    0 0 9 1
    "paper-audit recomputation does not manufacture downstream legal/policy authority"

h1MeasurementRepairStillReacquires :
  Diagnosis.brownRevision Outcome.observationConflict ≡ Revision.reacquireObservation
h1MeasurementRepairStillReacquires = Diagnosis.measurementConflictRequestsReacquisition

h5ModelRepairStillRevisesModel :
  Diagnosis.brownRevision Outcome.modelConflict ≡ Revision.reviseModel
h5ModelRepairStillRevisesModel = Diagnosis.confoundingConflictRequestsModelRevision

outcomeToH1PathRetained :
  Closure.AffectedClosure
    Brown.BrownDepends Brown.outcomeMeasurementEvidence Brown.h1AssociationClaim
outcomeToH1PathRetained = Lineage.outcomeToH1Path

exposureToH1PathRetained :
  Closure.AffectedClosure
    Brown.BrownDepends Brown.exposureMeasurementEvidence Brown.h1AssociationClaim
exposureToH1PathRetained = Lineage.exposureToH1Path

confoundingToH5PathRetained :
  Closure.AffectedClosure
    Brown.BrownDepends Brown.confoundingModelEvidence Brown.h5AdjustedAssociationClaim
confoundingToH5PathRetained = Lineage.confoundingToH5Path

data H1OutcomeChangeInvalidatesH5 : Set where
data H1ReactivationDeletesExposureAudit : Set where
data ParetoPreferredPaperRepairTransfersPolicyAuthority : Set where

h1OutcomeChangeDoesNotInvalidateH5 : H1OutcomeChangeInvalidatesH5 → ⊥
h1OutcomeChangeDoesNotInvalidateH5 ()

h1ReactivationDoesNotDeleteExposureAudit : H1ReactivationDeletesExposureAudit → ⊥
h1ReactivationDoesNotDeleteExposureAudit ()

paretoPreferenceDoesNotTransferPolicyAuthority :
  ParetoPreferredPaperRepairTransfersPolicyAuthority → ⊥
paretoPreferenceDoesNotTransferPolicyAuthority ()

record JohnBrownSelectiveInvalidationParetoBoundary : Set where
  constructor john-brown-selective-invalidation-pareto-boundary
  field
    currentH1OutcomePathMayBeMustRecompute : Bool
    historicalH1ExposurePathMayRemainRetained : Bool
    unrelatedH5ConfoundingPathMayRemainUnaffected : Bool
    H1ConsumerReviewMayRemainConditional : Bool
    policyAuthorityRemainsSeparate : Bool
    paretoRankingInvalidatesWholePaper : Bool
    ambientParetoCapacityForcesAllH1ToH5Materialisation : Bool

canonicalJohnBrownSelectiveInvalidationParetoBoundary :
  JohnBrownSelectiveInvalidationParetoBoundary
canonicalJohnBrownSelectiveInvalidationParetoBoundary =
  john-brown-selective-invalidation-pareto-boundary
    true true true true true false false
