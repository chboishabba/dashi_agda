module DASHI.Core.SourceExactFrontierBidiCrossPollination2026 where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Analysis.RiemannAristotleG2CurrentCutExact as RH
import DASHI.Physics.Closure.NSTriadKNHighestAlphaFrontierRound285Exact as NS
import DASHI.Physics.YangMills.BalabanUnifiedPresentCutSchwingerRecoveryRound140Exact as YM
import DASHI.Analysis.DeBruijnNewman2026SourceWeldExact as DBN
import DASHI.Mathematics.NumberTheory.PrimePowerDiophantineTuple2026SourceExact as Dujella
import DASHI.Core.ExternalAutoformalizationProvenanceExact as Auto

------------------------------------------------------------------------
-- REPOSITORY-NATIVE BIDI CROSS-POLLINATION
--
-- This is a DASHI theorem-pattern owner, not a theorem attributed to Dujella,
-- Polymath, Platt-Trudgian, Gomila, the RH Lean contributors, Navier-Stokes
-- authors, Balaban, or any AI system.
--
-- Shared architecture exposed by the current frontiers:
--
--   forward: exact source producer / certificate / proof leaf
--              -> same-object weld -> existing compiler -> consumer
--
--   backward: exact consumer
--              -> irreducible required leaf / equality / budget
--              -> source reconstruction or experiment/certificate
--
-- A source label, matching prose, external kernel receipt, or numerical
-- certificate cannot manufacture the missing same-object or theorem bridge.
------------------------------------------------------------------------

data EvidenceState : Set where
  announcementOnly : EvidenceState
  sourceExactRecovered : EvidenceState

data CoarseAnnouncementSurface : Set where
  samePublicClaimSurface : CoarseAnnouncementSurface

data FineEvidenceStatus : Set where
  announcementStatus : FineEvidenceStatus
  sourceExactStatus : FineEvidenceStatus

coarseAnnouncement : EvidenceState → CoarseAnnouncementSurface
coarseAnnouncement _ = samePublicClaimSurface

fineEvidence : EvidenceState → FineEvidenceStatus
fineEvidence announcementOnly = announcementStatus
fineEvidence sourceExactRecovered = sourceExactStatus

fineEvidenceDiffers :
  fineEvidence announcementOnly ≡ fineEvidence sourceExactRecovered → ⊥
fineEvidenceDiffers ()

announcementNonFactorability :
  INF.NonFactorabilityWitness coarseAnnouncement fineEvidence
announcementNonFactorability =
  INF.nonFactorabilityWitness
    announcementOnly sourceExactRecovered refl fineEvidenceDiffers

announcementCannotRecoverSourceExactness :
  INF.FactorsThrough coarseAnnouncement fineEvidence → ⊥
announcementCannotRecoverSourceExactness =
  INF.witnessRulesOutEveryFlatFactorisation announcementNonFactorability

------------------------------------------------------------------------
-- External verification itself is another fibre: checked Lean / exact Python
-- interval replay / source theorem statements remain distinct from Agda proof
-- terms and from statement correspondence.
------------------------------------------------------------------------

data VerificationCarrier : Set where
  externalKernelReceipt : VerificationCarrier
  externalExactCertificate : VerificationCarrier
  agdaProofTerm : VerificationCarrier
  correspondenceReceipt : VerificationCarrier

externalKernelNotAgdaProof : externalKernelReceipt ≡ agdaProofTerm → ⊥
externalKernelNotAgdaProof ()

externalCertificateNotAgdaProof : externalExactCertificate ≡ agdaProofTerm → ⊥
externalCertificateNotAgdaProof ()

correspondenceNotAgdaProof : correspondenceReceipt ≡ agdaProofTerm → ⊥
correspondenceNotAgdaProof ()

------------------------------------------------------------------------
-- RH specialization: the current G2 cut explicitly keeps checked Lean
-- provenance distinct from transported Agda proof terms, and retains one open
-- target-centred harmonic-analysis leaf plus a proved balance no-go.
------------------------------------------------------------------------

rhLeanProofsRemainExternal :
  RH.leanProofsTransportedIntoAgda RH.canonicalAristotleG2CurrentCut ≡ false
rhLeanProofsRemainExternal =
  RH.leanProofsTransportedIntoAgdaIsFalse RH.canonicalAristotleG2CurrentCut

rhTargetCenteredHarmonicLeafStillOpen :
  RH.targetCenteredLocalZeroExponentialSumBoundClosed RH.canonicalAristotleG2CurrentCut
  ≡ false
rhTargetCenteredHarmonicLeafStillOpen =
  RH.targetCenteredLocalZeroExponentialSumBoundClosedIsFalse
    RH.canonicalAristotleG2CurrentCut

rhOldStrictBalanceConsumerRejected :
  RH.strictOffEnergyBelowClusterUnderUnbrokenBalanceAdmissible
    RH.canonicalAristotleG2CurrentCut
  ≡ false
rhOldStrictBalanceConsumerRejected =
  RH.strictOffEnergyBelowClusterUnderUnbrokenBalanceAdmissibleIsFalse
    RH.canonicalAristotleG2CurrentCut

------------------------------------------------------------------------
-- NS specialization: BIDI pressure-testing has already rejected a plausible
-- bounded-critical route and isolated the direct critical-cone covariance leaf.
------------------------------------------------------------------------

nsBoundedCriticalRouteRejected =
  NS.round285BoundedAlmostPeriodicPersistentBadRouteRejected

nsDirectPhysicalRouteHighestAlpha =
  NS.round285DirectPhysicalCoherentDebtRouteHighestAlpha

nsCriticalConeSignedCovarianceStillOpen :
  NS.round285PhysicalCriticalConeSignedCovarianceClosed ≡ false
nsCriticalConeSignedCovarianceStillOpen =
  NS.round285PhysicalCriticalConeSignedCovarianceClosedIsFalse

------------------------------------------------------------------------
-- YM specialization: generic compiler work is downstream of literal physical
-- source instantiation.  The current same-action/history/stress compiler is
-- machine checked, while literal inhabitation remains conditional.
------------------------------------------------------------------------

ymUnifiedCompilerLevel = YM.unifiedPresentCutSchwingerRecoveryCompilerLevel
ymLiteralUnifiedRecoveryLevel = YM.literalUnifiedPresentCutSchwingerRecoveryLevel

------------------------------------------------------------------------
-- 2026 result specializations.
------------------------------------------------------------------------

dbnCertificateReplayStillExternal :
  DBN.candidateCertificateReplayOwnedInAgda ≡ false
dbnCertificateReplayStillExternal =
  DBN.candidateCertificateReplayOwnedInAgdaIsFalse

dujellaFullProofStillExternal :
  Dujella.fullDujellaProofReconstructedInAgda ≡ false
dujellaFullProofStillExternal =
  Dujella.fullDujellaProofReconstructedInAgdaIsFalse

------------------------------------------------------------------------
-- The generic consequence is deliberately modest but reusable:
--
--   same announcement / same theorem name / same output number
--       -/-> same proof stage;
--   external kernel or exact numerical certificate
--       -/-> Agda proof term;
--   no-go/refutation of one consumer
--       -> change the route rather than relabel the failed premise;
--   downstream compiler closure
--       -/-> source leaf inhabitation.
--
-- `Auto.PromotionReceipt` remains the generic promotion surface; this module
-- does not manufacture one from any domain-specific status above.
------------------------------------------------------------------------

autoformalizationPromotionRemainsSeparate : Set

autoformalizationPromotionRemainsSeparate = Auto.PromotionReceipt
