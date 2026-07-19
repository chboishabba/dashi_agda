module DASHI.Biology.Levin.AtavisticTranscriptomicDissociation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.IntersectionalLongitudinalResidualDynamics as Longitudinal
import DASHI.Biology.EpigeneticTemporalRegulationBridge as Epigenetic
import DASHI.Biology.Levin.MultiscaleIdentityDissociation as Identity

------------------------------------------------------------------------
-- Tissue divergence in phylogenetic/transcriptomic age assignments.

record PhylostratigraphicConcordanceStudy : Set where
  field
    tissuesIndexed                 : Bool
    chronologicalAgeIndexed        : Bool
    geneAgeAssignmentSpecified     : Bool
    expressionWeightingSpecified   : Bool
    youngConcordanceMeasured       : Bool
    ageRelatedDivergenceMeasured   : Bool
    tissueHeterogeneityRetained    : Bool
    batchAndCellCompositionControlled : Bool
    interpretation                 : String

record AtavisticDissociationBoundary : Set where
  field
    longitudinalLane : Longitudinal.IntersectionalLongitudinalResidualDynamicsBoundary
    epigeneticLane   : Epigenetic.EpigeneticTemporalRegulationBoundary
    identityLane     : Identity.MultiscaleIdentityDissociationBoundary
    evolutionaryAgeNotChronologicalAge : Bool
    divergenceNotLiteralCellBelief : Bool
    transcriptomicShiftNotDedifferentiationByDefinition : Bool
    concordanceLossNotSoleCauseOfAging : Bool
    cancerAnalogyNotUniversalMechanism : Bool
    clinicalUseNeedsProspectiveValidation : Bool

canonicalAtavisticDissociationBoundary : AtavisticDissociationBoundary
canonicalAtavisticDissociationBoundary = record
  { longitudinalLane = Longitudinal.canonicalIntersectionalLongitudinalResidualDynamicsBoundary
  ; epigeneticLane = Epigenetic.canonicalEpigeneticTemporalRegulationBoundary
  ; identityLane = Identity.canonicalMultiscaleIdentityDissociationBoundary
  ; evolutionaryAgeNotChronologicalAge = true
  ; divergenceNotLiteralCellBelief = true
  ; transcriptomicShiftNotDedifferentiationByDefinition = true
  ; concordanceLossNotSoleCauseOfAging = true
  ; cancerAnalogyNotUniversalMechanism = true
  ; clinicalUseNeedsProspectiveValidation = true
  }
