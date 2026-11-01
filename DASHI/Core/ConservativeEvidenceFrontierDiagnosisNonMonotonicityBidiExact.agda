module DASHI.Core.ConservativeEvidenceFrontierDiagnosisNonMonotonicityBidiExact where

open import DASHI.Core.Prelude

import DASHI.Core.AristotleFrontierWorklistTruthMaintenanceBridgeExact as Aristotle
import DASHI.Core.TemporalDiagnosisFibreProjectionBidiExact as Diagnosis
import DASHI.Core.IncrementalDiagnosisTruthMaintenanceBidiExact as Truth

------------------------------------------------------------------------
-- CONSERVATIVE EVIDENCE FRONTIER != DIAGNOSIS FRONTIER
--
-- The uploaded Aristotle corpus rounds exhibit a gap/frontier that shrinks as
-- conservative evidence is added and prior entailments are retained. DASHI's
-- temporal diagnosis fibre is a different object: append-only history may
-- project to a larger current diagnosis fibre when later evidence reactivates a
-- previously eliminated diagnosis.
------------------------------------------------------------------------

data FrontierKind : Set where
  corpusGapFrontier : FrontierKind
  diagnosisFibreFrontier : FrontierKind

record FrontierEvolutionBoundary : Set where
  constructor frontier-evolution-boundary
  field
    conservativeCorpusExtensionMayRetainOldEntailments : Bool
    corpusGapFrontierMayShrinkAcrossRounds : Bool
    appendOnlyDiagnosisHistoryMayExpandCurrentDiagnosisFibre : Bool
    everyFrontierMustMonotonicallyShrink : Bool
    evidenceCarrierMonotonicityImpliesConclusionMonotonicity : Bool
    frontierKindMustBeDeclared : Bool

canonicalFrontierEvolutionBoundary : FrontierEvolutionBoundary
canonicalFrontierEvolutionBoundary =
  frontier-evolution-boundary true true true false false true

aristotleMethodologyRetained : Aristotle.AristotleMethodologyDonor
aristotleMethodologyRetained = Aristotle.canonicalAristotleMethodologyDonor

diagnosisProjectionBoundaryRetained : Diagnosis.TemporalDiagnosisProjectionBoundary
diagnosisProjectionBoundaryRetained = Diagnosis.canonicalTemporalDiagnosisProjectionBoundary

truthMaintenanceBoundaryRetained : Truth.IncrementalTruthMaintenanceBoundary
truthMaintenanceBoundaryRetained = Truth.canonicalIncrementalTruthMaintenanceBoundary

data ConservativeExtensionForcesDiagnosisNarrowing : Set where
data DiagnosisReactivationDeletesEvidenceHistory : Set where
data ShrinkingCorpusGapMeansAllFrontiersShrink : Set where

conservativeExtensionDoesNotForceDiagnosisNarrowing :
  ConservativeExtensionForcesDiagnosisNarrowing → ⊥
conservativeExtensionDoesNotForceDiagnosisNarrowing ()

diagnosisReactivationDoesNotDeleteEvidenceHistory :
  DiagnosisReactivationDeletesEvidenceHistory → ⊥
diagnosisReactivationDoesNotDeleteEvidenceHistory ()

corpusGapShrinkageDoesNotGeneralizeToEveryFrontier :
  ShrinkingCorpusGapMeansAllFrontiersShrink → ⊥
corpusGapShrinkageDoesNotGeneralizeToEveryFrontier ()
