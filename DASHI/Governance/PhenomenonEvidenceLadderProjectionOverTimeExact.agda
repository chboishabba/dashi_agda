module DASHI.Governance.PhenomenonEvidenceLadderProjectionOverTimeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal
import DASHI.Governance.AnomalousPhenomenonTemporalEvidenceTrajectoriesExact as Trajectory

------------------------------------------------------------------------
-- TIME-SLICED EVIDENCE LADDER
--
-- The eight-coordinate ladder is an observer of the temporal fibre.  It is not
-- a substitute for the live interpretations or their ordered evidence path.
------------------------------------------------------------------------

standingAt :
  Trajectory.EvidenceMoment →
  Temporal.EvidenceCoordinate →
  Temporal.CoordinateStanding

-- High-rigour Bem replication: original robust effect is downgraded; methods
-- and reporting are strong, but mechanism/ontology are not thereby supplied.
standingAt Trajectory.transparentPsi2025 Temporal.reportReliability = Temporal.empiricallySupported
standingAt Trajectory.transparentPsi2025 Temporal.anomalyStrength = Temporal.downgraded
standingAt Trajectory.transparentPsi2025 Temporal.controlStrength = Temporal.empiricallySupported
standingAt Trajectory.transparentPsi2025 Temporal.independentReplication = Temporal.downgraded
standingAt Trajectory.transparentPsi2025 Temporal.mechanismDiscrimination = Temporal.unresolved
standingAt Trajectory.transparentPsi2025 Temporal.generalisation = Temporal.unsupported
standingAt Trajectory.transparentPsi2025 Temporal.operationalUtility = Temporal.unsupported
standingAt Trajectory.transparentPsi2025 Temporal.ontologicalInference = Temporal.unsupported

-- Presentiment update: aggregate anomaly remains reported but interpretation is
-- contested; mechanism and broader utility remain open.
standingAt Trajectory.presentimentUpdate2018 Temporal.reportReliability = Temporal.empiricallySupported
standingAt Trajectory.presentimentUpdate2018 Temporal.anomalyStrength = Temporal.contested
standingAt Trajectory.presentimentUpdate2018 Temporal.controlStrength = Temporal.contested
standingAt Trajectory.presentimentUpdate2018 Temporal.independentReplication = Temporal.contested
standingAt Trajectory.presentimentUpdate2018 Temporal.mechanismDiscrimination = Temporal.unresolved
standingAt Trajectory.presentimentUpdate2018 Temporal.generalisation = Temporal.unresolved
standingAt Trajectory.presentimentUpdate2018 Temporal.operationalUtility = Temporal.unsupported
standingAt Trajectory.presentimentUpdate2018 Temporal.ontologicalInference = Temporal.unsupported

-- STARGATE at operational review: programme/session evidence is real, but the
-- reliable intelligence-channel claim is downgraded.
standingAt Trajectory.stargateOperationalReview1995 Temporal.reportReliability = Temporal.empiricallySupported
standingAt Trajectory.stargateOperationalReview1995 Temporal.anomalyStrength = Temporal.contested
standingAt Trajectory.stargateOperationalReview1995 Temporal.controlStrength = Temporal.contested
standingAt Trajectory.stargateOperationalReview1995 Temporal.independentReplication = Temporal.contested
standingAt Trajectory.stargateOperationalReview1995 Temporal.mechanismDiscrimination = Temporal.unresolved
standingAt Trajectory.stargateOperationalReview1995 Temporal.generalisation = Temporal.downgraded
standingAt Trajectory.stargateOperationalReview1995 Temporal.operationalUtility = Temporal.downgraded
standingAt Trajectory.stargateOperationalReview1995 Temporal.ontologicalInference = Temporal.unsupported

-- Ganzfeld: retained as a contested anomaly rather than either settled psi or a
-- null theorem.
standingAt Trajectory.ganzfeldContestedCurrent Temporal.reportReliability = Temporal.empiricallySupported
standingAt Trajectory.ganzfeldContestedCurrent Temporal.anomalyStrength = Temporal.contested
standingAt Trajectory.ganzfeldContestedCurrent Temporal.controlStrength = Temporal.contested
standingAt Trajectory.ganzfeldContestedCurrent Temporal.independentReplication = Temporal.contested
standingAt Trajectory.ganzfeldContestedCurrent Temporal.mechanismDiscrimination = Temporal.unresolved
standingAt Trajectory.ganzfeldContestedCurrent Temporal.generalisation = Temporal.unresolved
standingAt Trajectory.ganzfeldContestedCurrent Temporal.operationalUtility = Temporal.unsupported
standingAt Trajectory.ganzfeldContestedCurrent Temporal.ontologicalInference = Temporal.unsupported

-- Psilocybin depression: repeated randomized/meta-analytic clinical signal is
-- stronger than in the early-modern phase, while expectancy/blinding,
-- mechanism, generalisation and metaphysical interpretation remain separate.
standingAt Trajectory.psilocybinEarlyModernTrials Temporal.reportReliability = Temporal.empiricallySupported
standingAt Trajectory.psilocybinEarlyModernTrials Temporal.anomalyStrength = Temporal.sourceReported
standingAt Trajectory.psilocybinEarlyModernTrials Temporal.controlStrength = Temporal.contested
standingAt Trajectory.psilocybinEarlyModernTrials Temporal.independentReplication = Temporal.contested
standingAt Trajectory.psilocybinEarlyModernTrials Temporal.mechanismDiscrimination = Temporal.unresolved
standingAt Trajectory.psilocybinEarlyModernTrials Temporal.generalisation = Temporal.unresolved
standingAt Trajectory.psilocybinEarlyModernTrials Temporal.operationalUtility = Temporal.contested
standingAt Trajectory.psilocybinEarlyModernTrials Temporal.ontologicalInference = Temporal.unsupported

standingAt Trajectory.psilocybinMeta2025_2026 Temporal.reportReliability = Temporal.empiricallySupported
standingAt Trajectory.psilocybinMeta2025_2026 Temporal.anomalyStrength = Temporal.empiricallySupported
standingAt Trajectory.psilocybinMeta2025_2026 Temporal.controlStrength = Temporal.contested
standingAt Trajectory.psilocybinMeta2025_2026 Temporal.independentReplication = Temporal.empiricallySupported
standingAt Trajectory.psilocybinMeta2025_2026 Temporal.mechanismDiscrimination = Temporal.unresolved
standingAt Trajectory.psilocybinMeta2025_2026 Temporal.generalisation = Temporal.contested
standingAt Trajectory.psilocybinMeta2025_2026 Temporal.operationalUtility = Temporal.contested
standingAt Trajectory.psilocybinMeta2025_2026 Temporal.ontologicalInference = Temporal.unsupported

-- AWARE-II: recalled experience/cognitive activity is empirically studyable;
-- visual-target evidence did not establish extracerebral perception.
standingAt Trajectory.awareII2023 Temporal.reportReliability = Temporal.empiricallySupported
standingAt Trajectory.awareII2023 Temporal.anomalyStrength = Temporal.sourceReported
standingAt Trajectory.awareII2023 Temporal.controlStrength = Temporal.empiricallySupported
standingAt Trajectory.awareII2023 Temporal.independentReplication = Temporal.contested
standingAt Trajectory.awareII2023 Temporal.mechanismDiscrimination = Temporal.unresolved
standingAt Trajectory.awareII2023 Temporal.generalisation = Temporal.unresolved
standingAt Trajectory.awareII2023 Temporal.operationalUtility = Temporal.unsupported
standingAt Trajectory.awareII2023 Temporal.ontologicalInference = Temporal.unsupported

-- All uninstantiated historical slices are deliberately unresolved here rather
-- than silently receiving the current rating.
standingAt _ _ = Temporal.unresolved

ladderAt :
  (t : Trajectory.EvidenceMoment) →
  Temporal.EvidenceLadderObservation Trajectory.temporalSystem t
ladderAt t = Temporal.evidenceLadderObservation
  (standingAt t)
  (Trajectory.momentReference t)

------------------------------------------------------------------------
-- The same coarse trajectory label can conceal changed ladder coordinates.
------------------------------------------------------------------------

psilocybinCoarseLabelStable :
  Trajectory.summaryAt Trajectory.psilocybinEarlyModernTrials
  ≡ Trajectory.summaryAt Trajectory.psilocybinMeta2025_2026
psilocybinCoarseLabelStable = refl

psilocybinReplicationCoordinateChanged :
  standingAt Trajectory.psilocybinEarlyModernTrials Temporal.independentReplication
  ≡ standingAt Trajectory.psilocybinMeta2025_2026 Temporal.independentReplication → ⊥
psilocybinReplicationCoordinateChanged ()

coarseSummaryCannotRecoverReplicationCoordinate :
  INF.FactorsThrough
    Trajectory.summaryAt
    (λ t → standingAt t Temporal.independentReplication) → ⊥
coarseSummaryCannotRecoverReplicationCoordinate =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      Trajectory.psilocybinEarlyModernTrials
      Trajectory.psilocybinMeta2025_2026
      refl
      psilocybinReplicationCoordinateChanged)

------------------------------------------------------------------------
-- Coordinate gains are non-promoting.
------------------------------------------------------------------------

data ReplicationGainPromotesMechanism : Set where

data ClinicalSignalPromotesOntology : Set where

data ExperienceReportPromotesExtracerebralMechanism : Set where

data HighControlPromotesOperationalUtility : Set where

replicationGainDoesNotPromoteMechanism : ReplicationGainPromotesMechanism → ⊥
replicationGainDoesNotPromoteMechanism ()

clinicalSignalDoesNotPromoteOntology : ClinicalSignalPromotesOntology → ⊥
clinicalSignalDoesNotPromoteOntology ()

experienceReportDoesNotPromoteExtracerebralMechanism :
  ExperienceReportPromotesExtracerebralMechanism → ⊥
experienceReportDoesNotPromoteExtracerebralMechanism ()

highControlDoesNotPromoteOperationalUtility : HighControlPromotesOperationalUtility → ⊥
highControlDoesNotPromoteOperationalUtility ()

record PhenomenonEvidenceLadderProjectionBoundary : Set where
  constructor phenomenonEvidenceLadderProjectionBoundary
  field
    ladderIsProjectionOfTemporalFibre : Bool
    ladderIsProjectionOfTemporalFibreIsTrue : ladderIsProjectionOfTemporalFibre ≡ true
    sameCoarseLabelImpliesSameCoordinates : Bool
    sameCoarseLabelImpliesSameCoordinatesIsFalse :
      sameCoarseLabelImpliesSameCoordinates ≡ false
    strongerReplicationAutomaticallyClosesMechanism : Bool
    strongerReplicationAutomaticallyClosesMechanismIsFalse :
      strongerReplicationAutomaticallyClosesMechanism ≡ false

canonicalPhenomenonEvidenceLadderProjectionBoundary :
  PhenomenonEvidenceLadderProjectionBoundary
canonicalPhenomenonEvidenceLadderProjectionBoundary =
  phenomenonEvidenceLadderProjectionBoundary true refl false refl false refl
