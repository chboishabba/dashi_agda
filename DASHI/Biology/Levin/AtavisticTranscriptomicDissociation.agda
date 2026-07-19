module DASHI.Biology.Levin.AtavisticTranscriptomicDissociation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.IntersectionalLongitudinalResidualDynamics as Longitudinal
import DASHI.Biology.EpigeneticTemporalRegulationBridge as Epigenetic
import DASHI.Biology.Levin.MultiscaleIdentityDissociation as Identity

------------------------------------------------------------------------
-- Tissue divergence in phylogenetic/transcriptomic age assignments.
-- Existing longitudinal, epigenetic, and multiscale-identity modules remain
-- upstream constraints; this file does not replace their richer carriers.

record PhylostratigraphicConcordanceStudy : Set where
  field
    tissuesIndexed                    : Bool
    chronologicalAgeIndexed           : Bool
    geneAgeAssignmentSpecified        : Bool
    expressionWeightingSpecified      : Bool
    youngConcordanceMeasured          : Bool
    ageRelatedDivergenceMeasured      : Bool
    tissueHeterogeneityRetained       : Bool
    batchAndCellCompositionControlled : Bool
    interpretation                    : String

record AtavisticDissociationBoundary : Set where
  field
    longitudinalLaneImported : Bool
    epigeneticLaneImported   : Bool
    identityLaneImported     : Bool
    evolutionaryAgeNotChronologicalAge : Bool
    divergenceNotLiteralCellBelief : Bool
    transcriptomicShiftNotDedifferentiationByDefinition : Bool
    concordanceLossNotSoleCauseOfAging : Bool
    cancerAnalogyNotUniversalMechanism : Bool
    clinicalUseNeedsProspectiveValidation : Bool

canonicalAtavisticDissociationBoundary : AtavisticDissociationBoundary
canonicalAtavisticDissociationBoundary = record
  { longitudinalLaneImported = true
  ; epigeneticLaneImported = true
  ; identityLaneImported = true
  ; evolutionaryAgeNotChronologicalAge = true
  ; divergenceNotLiteralCellBelief = true
  ; transcriptomicShiftNotDedifferentiationByDefinition = true
  ; concordanceLossNotSoleCauseOfAging = true
  ; cancerAnalogyNotUniversalMechanism = true
  ; clinicalUseNeedsProspectiveValidation = true
  }
