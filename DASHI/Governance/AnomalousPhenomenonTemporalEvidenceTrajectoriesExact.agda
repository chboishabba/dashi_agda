module DASHI.Governance.AnomalousPhenomenonTemporalEvidenceTrajectoriesExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.HistoryConditionedChoiceExact as HistoryChoice
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal

------------------------------------------------------------------------
-- SOURCE-BOUNDED TEMPORAL EVIDENCE TRAJECTORIES
--
-- These finite fibres model how live interpretations change across selected
-- historical evidence moments.  They are deliberately not exhaustive Bayesian
-- posteriors and do not assign metaphysical truth values.
------------------------------------------------------------------------

data Phenomenon : Set where
  bemPrecognition
  presentimentPhysiology
  stargateRemoteViewing
  ganzfeldPsi
  psilocybinDepression
  ndeCardiacArrestConsciousness
  : Phenomenon

data EvidenceMoment : Set where
  bemInitial2011
  transparentPsi2025
  presentimentMeta2012
  presentimentUpdate2018
  stargateExperimentalEra
  stargateOperationalReview1995
  ganzfeldPositiveMetaEra
  ganzfeldContestedCurrent
  psilocybinEarlyModernTrials
  psilocybinMeta2025_2026
  ndeProspective2001
  awareII2023
  : EvidenceMoment

momentPhenomenon : EvidenceMoment → Phenomenon
momentPhenomenon bemInitial2011 = bemPrecognition
momentPhenomenon transparentPsi2025 = bemPrecognition
momentPhenomenon presentimentMeta2012 = presentimentPhysiology
momentPhenomenon presentimentUpdate2018 = presentimentPhysiology
momentPhenomenon stargateExperimentalEra = stargateRemoteViewing
momentPhenomenon stargateOperationalReview1995 = stargateRemoteViewing
momentPhenomenon ganzfeldPositiveMetaEra = ganzfeldPsi
momentPhenomenon ganzfeldContestedCurrent = ganzfeldPsi
momentPhenomenon psilocybinEarlyModernTrials = psilocybinDepression
momentPhenomenon psilocybinMeta2025_2026 = psilocybinDepression
momentPhenomenon ndeProspective2001 = ndeCardiacArrestConsciousness
momentPhenomenon awareII2023 = ndeCardiacArrestConsciousness

data Interpretation : Set where
  robustBemPrecognition
  oneTimeBemAnomaly
  bemMethodArtifact

  anticipatoryPhysiologyAnomaly
  presentimentMethodArtifact

  reliableRemoteViewingChannel
  unreliableRemoteViewingAnomaly
  remoteViewingMethodArtifact

  ganzfeldSmallAnomaly
  ganzfeldMethodArtifact

  noPsilocybinTherapeuticEffect
  psilocybinTherapeuticEffect
  expectancyBlindingContribution

  noRecalledExperienceDuringCardiacArrest
  recalledExperienceDuringCardiacArrest
  brainBasedCriticalStateMechanism
  extracerebralInterpretation
  : Interpretation

------------------------------------------------------------------------
-- Live fibres at selected moments.
------------------------------------------------------------------------

Compatible : EvidenceMoment → Interpretation → Set

Compatible bemInitial2011 robustBemPrecognition = ⊤
Compatible bemInitial2011 oneTimeBemAnomaly = ⊤
Compatible bemInitial2011 bemMethodArtifact = ⊤
Compatible transparentPsi2025 robustBemPrecognition = ⊥
Compatible transparentPsi2025 oneTimeBemAnomaly = ⊤
Compatible transparentPsi2025 bemMethodArtifact = ⊤

Compatible presentimentMeta2012 anticipatoryPhysiologyAnomaly = ⊤
Compatible presentimentMeta2012 presentimentMethodArtifact = ⊤
Compatible presentimentUpdate2018 anticipatoryPhysiologyAnomaly = ⊤
Compatible presentimentUpdate2018 presentimentMethodArtifact = ⊤

Compatible stargateExperimentalEra reliableRemoteViewingChannel = ⊤
Compatible stargateExperimentalEra unreliableRemoteViewingAnomaly = ⊤
Compatible stargateExperimentalEra remoteViewingMethodArtifact = ⊤
Compatible stargateOperationalReview1995 reliableRemoteViewingChannel = ⊥
Compatible stargateOperationalReview1995 unreliableRemoteViewingAnomaly = ⊤
Compatible stargateOperationalReview1995 remoteViewingMethodArtifact = ⊤

Compatible ganzfeldPositiveMetaEra ganzfeldSmallAnomaly = ⊤
Compatible ganzfeldPositiveMetaEra ganzfeldMethodArtifact = ⊤
Compatible ganzfeldContestedCurrent ganzfeldSmallAnomaly = ⊤
Compatible ganzfeldContestedCurrent ganzfeldMethodArtifact = ⊤

Compatible psilocybinEarlyModernTrials noPsilocybinTherapeuticEffect = ⊤
Compatible psilocybinEarlyModernTrials psilocybinTherapeuticEffect = ⊤
Compatible psilocybinEarlyModernTrials expectancyBlindingContribution = ⊤
Compatible psilocybinMeta2025_2026 noPsilocybinTherapeuticEffect = ⊥
Compatible psilocybinMeta2025_2026 psilocybinTherapeuticEffect = ⊤
Compatible psilocybinMeta2025_2026 expectancyBlindingContribution = ⊤

Compatible ndeProspective2001 noRecalledExperienceDuringCardiacArrest = ⊤
Compatible ndeProspective2001 recalledExperienceDuringCardiacArrest = ⊤
Compatible ndeProspective2001 brainBasedCriticalStateMechanism = ⊤
Compatible ndeProspective2001 extracerebralInterpretation = ⊤
Compatible awareII2023 noRecalledExperienceDuringCardiacArrest = ⊥
Compatible awareII2023 recalledExperienceDuringCardiacArrest = ⊤
Compatible awareII2023 brainBasedCriticalStateMechanism = ⊤
Compatible awareII2023 extracerebralInterpretation = ⊤

Compatible _ _ = ⊥

------------------------------------------------------------------------
-- Coarse current summaries intentionally erase path structure.
------------------------------------------------------------------------

data CurrentSummary : Set where
  downgradedButResidualOpen
  contestedAnomaly
  developingClinicalEvidence
  experienceEstablishedMechanismOpen
  : CurrentSummary

summaryAt : EvidenceMoment → CurrentSummary
summaryAt bemInitial2011 = contestedAnomaly
summaryAt transparentPsi2025 = downgradedButResidualOpen
summaryAt presentimentMeta2012 = contestedAnomaly
summaryAt presentimentUpdate2018 = contestedAnomaly
summaryAt stargateExperimentalEra = contestedAnomaly
summaryAt stargateOperationalReview1995 = downgradedButResidualOpen
summaryAt ganzfeldPositiveMetaEra = contestedAnomaly
summaryAt ganzfeldContestedCurrent = contestedAnomaly
summaryAt psilocybinEarlyModernTrials = developingClinicalEvidence
summaryAt psilocybinMeta2025_2026 = developingClinicalEvidence
summaryAt ndeProspective2001 = experienceEstablishedMechanismOpen
summaryAt awareII2023 = experienceEstablishedMechanismOpen

momentReference : EvidenceMoment → String
momentReference bemInitial2011 = "Bem 2011 precognition experiments"
momentReference transparentPsi2025 = "Walleczek et al. 2025 AMP/Transparent Psi replication, DOI 10.1371/journal.pone.0335330"
momentReference presentimentMeta2012 = "Mossbridge et al. 2012 presentiment meta-analysis, PMID 23109927"
momentReference presentimentUpdate2018 = "Tressoldi et al. 2018 presentiment meta-analysis update, PMID 30228876"
momentReference stargateExperimentalEra = "STARGATE/GRILL FLAME experimental record era"
momentReference stargateOperationalReview1995 = "1995 STARGATE operational evaluation / CIA programme decision"
momentReference ganzfeldPositiveMetaEra = "Ganzfeld/free-response positive meta-analytic era"
momentReference ganzfeldContestedCurrent = "Ganzfeld evidence retained as contested pending stronger adversarial replication"
momentReference psilocybinEarlyModernTrials = "early modern randomized psilocybin depression trials"
momentReference psilocybinMeta2025_2026 = "2025-2026 psilocybin depression meta-analyses including PMID 39627679 and PMID 41876058"
momentReference ndeProspective2001 = "van Lommel et al. 2001 prospective cardiac-arrest NDE study, PMID 11755611"
momentReference awareII2023 = "AWARE-II 2023, PMID 37423492"

temporalSystem : Temporal.TemporalEvidenceSystem
temporalSystem = record
  { Temporal.Time = EvidenceMoment
  ; Temporal.Interpretation = Interpretation
  ; Temporal.Compatible = Compatible
  ; Temporal.Summary = CurrentSummary
  ; Temporal.summarize = summaryAt
  ; Temporal.timeReference = momentReference
  }

------------------------------------------------------------------------
-- Concrete fibre transitions.
------------------------------------------------------------------------

bemReplicationStrictlyRemovesRobustOriginalEffect :
  Temporal.StrictFibreRefinement temporalSystem bemInitial2011 transparentPsi2025
bemReplicationStrictlyRemovesRobustOriginalEffect = record
  { Temporal.refinement = record
      { Temporal.retainedWasPreviouslyLive = λ
          { robustBemPrecognition ()
          ; oneTimeBemAnomaly _ → tt
          ; bemMethodArtifact _ → tt
          ; _ ()
          }
      }
  ; Temporal.removedInterpretation = robustBemPrecognition
  ; Temporal.removedWasLive = tt
  ; Temporal.removedIsNoLongerLive = λ ()
  }

stargateOperationalReviewRemovesReliableOperationalChannel :
  Temporal.StrictFibreRefinement
    temporalSystem stargateExperimentalEra stargateOperationalReview1995
stargateOperationalReviewRemovesReliableOperationalChannel = record
  { Temporal.refinement = record
      { Temporal.retainedWasPreviouslyLive = λ
          { reliableRemoteViewingChannel ()
          ; unreliableRemoteViewingAnomaly _ → tt
          ; remoteViewingMethodArtifact _ → tt
          ; _ ()
          }
      }
  ; Temporal.removedInterpretation = reliableRemoteViewingChannel
  ; Temporal.removedWasLive = tt
  ; Temporal.removedIsNoLongerLive = λ ()
  }

presentimentUpdateLeavesCoreInterpretationFibreOpen :
  Temporal.FibreUnchanged temporalSystem presentimentMeta2012 presentimentUpdate2018
presentimentUpdateLeavesCoreInterpretationFibreOpen = record
  { Temporal.forward = λ
      { anticipatoryPhysiologyAnomaly _ → tt
      ; presentimentMethodArtifact _ → tt
      ; _ ()
      }
  ; Temporal.backward = λ
      { anticipatoryPhysiologyAnomaly _ → tt
      ; presentimentMethodArtifact _ → tt
      ; _ ()
      }
  }

psilocybinMetaEvidenceRemovesPureNoEffectInterpretation :
  Temporal.StrictFibreRefinement
    temporalSystem psilocybinEarlyModernTrials psilocybinMeta2025_2026
psilocybinMetaEvidenceRemovesPureNoEffectInterpretation = record
  { Temporal.refinement = record
      { Temporal.retainedWasPreviouslyLive = λ
          { noPsilocybinTherapeuticEffect ()
          ; psilocybinTherapeuticEffect _ → tt
          ; expectancyBlindingContribution _ → tt
          ; _ ()
          }
      }
  ; Temporal.removedInterpretation = noPsilocybinTherapeuticEffect
  ; Temporal.removedWasLive = tt
  ; Temporal.removedIsNoLongerLive = λ ()
  }

awareIIRemovesNoRecalledExperienceInterpretation :
  Temporal.StrictFibreRefinement temporalSystem ndeProspective2001 awareII2023
awareIIRemovesNoRecalledExperienceInterpretation = record
  { Temporal.refinement = record
      { Temporal.retainedWasPreviouslyLive = λ
          { noRecalledExperienceDuringCardiacArrest ()
          ; recalledExperienceDuringCardiacArrest _ → tt
          ; brainBasedCriticalStateMechanism _ → tt
          ; extracerebralInterpretation _ → tt
          ; _ ()
          }
      }
  ; Temporal.removedInterpretation = noRecalledExperienceDuringCardiacArrest
  ; Temporal.removedWasLive = tt
  ; Temporal.removedIsNoLongerLive = λ ()
  }

------------------------------------------------------------------------
-- Ordered evidence paths retain the update type and reference.
------------------------------------------------------------------------

bemReplicationTransition :
  Temporal.EvidenceTransition temporalSystem bemInitial2011 transparentPsi2025
bemReplicationTransition = Temporal.evidenceTransition
  Temporal.failedReplication
  "AMP/Transparent Psi high-powered replication"
  true refl

presentimentMetaUpdateTransition :
  Temporal.EvidenceTransition temporalSystem presentimentMeta2012 presentimentUpdate2018
presentimentMetaUpdateTransition = Temporal.evidenceTransition
  Temporal.metaAnalysis
  "2018 update to the anticipatory-physiology meta-analysis"
  true refl

psilocybinMetaTransition :
  Temporal.EvidenceTransition temporalSystem psilocybinEarlyModernTrials psilocybinMeta2025_2026
psilocybinMetaTransition = Temporal.evidenceTransition
  Temporal.metaAnalysis
  "2025-2026 randomized-trial meta-analytic evidence"
  true refl

bemEvidencePath : Temporal.EvidencePath temporalSystem bemInitial2011 transparentPsi2025
bemEvidencePath = Temporal.pathStep bemReplicationTransition Temporal.pathId

presentimentEvidencePath :
  Temporal.EvidencePath temporalSystem presentimentMeta2012 presentimentUpdate2018
presentimentEvidencePath = Temporal.pathStep presentimentMetaUpdateTransition Temporal.pathId

psilocybinEvidencePath :
  Temporal.EvidencePath temporalSystem psilocybinEarlyModernTrials psilocybinMeta2025_2026
psilocybinEvidencePath = Temporal.pathStep psilocybinMetaTransition Temporal.pathId

------------------------------------------------------------------------
-- Same present coarse label, different path -> different next experiment.
------------------------------------------------------------------------

data PresentHistory : Set where
  presentimentHistory ganzfeldHistory : PresentHistory

data PresentPattern : Set where
  repeatedPhysiologyMetaPath longstandingFreeResponsePath : PresentPattern

data NextExperiment : Set where
  preregisteredPhysiologyReplication adversarialGanzfeldReplication : NextExperiment

historyChoiceSurface : HistoryChoice.HistoryConditionedChoiceSurface
historyChoiceSurface = record
  { HistoryChoice.History = PresentHistory
  ; HistoryChoice.Observation = CurrentSummary
  ; HistoryChoice.Pattern = PresentPattern
  ; HistoryChoice.Choice = NextExperiment
  ; HistoryChoice.observe = λ _ → contestedAnomaly
  ; HistoryChoice.patternOf = λ
      { presentimentHistory → repeatedPhysiologyMetaPath
      ; ganzfeldHistory → longstandingFreeResponsePath
      }
  ; HistoryChoice.choose = λ
      { presentimentHistory → preregisteredPhysiologyReplication
      ; ganzfeldHistory → adversarialGanzfeldReplication
      }
  ; HistoryChoice.historyReading =
      "Presentiment and Ganzfeld can share a coarse contested-anomaly label while their evidence paths demand different next experiments."
  }

samePresentDifferentNextExperiment :
  HistoryChoice.DistinctHistoriesSameObservationDifferentChoice historyChoiceSurface
samePresentDifferentNextExperiment = record
  { HistoryChoice.leftHistory = presentimentHistory
  ; HistoryChoice.rightHistory = ganzfeldHistory
  ; HistoryChoice.historiesDistinct = λ ()
  ; HistoryChoice.samePresentObservation = refl
  ; HistoryChoice.choicesDiffer = λ ()
  }

presentLabelCannotDetermineNextExperiment :
  INF.FactorsThrough
    (HistoryChoice.observe historyChoiceSurface)
    (HistoryChoice.choose historyChoiceSurface) → ⊥
presentLabelCannotDetermineNextExperiment =
  HistoryChoice.historySensitiveChoiceCannotDescendThroughPresentObservation
    samePresentDifferentNextExperiment

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data CurrentLabelPromotesWholeEvidenceHistory : Set where

data StatisticalAnomalyPromotesPsiMechanism : Set where

data TherapeuticEffectPromotesMetaphysicalTruth : Set where

data RecalledExperiencePromotesExtracerebralPerception : Set where

currentLabelDoesNotPromoteWholeHistory : CurrentLabelPromotesWholeEvidenceHistory → ⊥
currentLabelDoesNotPromoteWholeHistory ()

statisticalAnomalyDoesNotPromotePsiMechanism : StatisticalAnomalyPromotesPsiMechanism → ⊥
statisticalAnomalyDoesNotPromotePsiMechanism ()

therapeuticEffectDoesNotPromoteMetaphysicalTruth : TherapeuticEffectPromotesMetaphysicalTruth → ⊥
therapeuticEffectDoesNotPromoteMetaphysicalTruth ()

recalledExperienceDoesNotPromoteExtracerebralPerception :
  RecalledExperiencePromotesExtracerebralPerception → ⊥
recalledExperienceDoesNotPromoteExtracerebralPerception ()

record AnomalousPhenomenonTemporalEvidenceBoundary : Set where
  constructor anomalousPhenomenonTemporalEvidenceBoundary
  field
    fibresAreTimeIndexed : Bool
    fibresAreTimeIndexedIsTrue : fibresAreTimeIndexed ≡ true
    laterEvidenceMayStrictlyRefine : Bool
    laterEvidenceMayStrictlyRefineIsTrue : laterEvidenceMayStrictlyRefine ≡ true
    laterEvidenceMustAlwaysShrink : Bool
    laterEvidenceMustAlwaysShrinkIsFalse : laterEvidenceMustAlwaysShrink ≡ false
    presentLabelDeterminesNextExperiment : Bool
    presentLabelDeterminesNextExperimentIsFalse : presentLabelDeterminesNextExperiment ≡ false

canonicalAnomalousPhenomenonTemporalEvidenceBoundary :
  AnomalousPhenomenonTemporalEvidenceBoundary
canonicalAnomalousPhenomenonTemporalEvidenceBoundary =
  anomalousPhenomenonTemporalEvidenceBoundary
    true refl true refl false refl false refl
