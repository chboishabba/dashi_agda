module DASHI.Education.DigitalESDSourceAuditHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Education.DigitalESDSourceAuditScaleExact as Scale
import DASHI.Education.DigitalESDSituatedAuditObserverExact as Observer
import DASHI.Education.DigitalESDSourceAuditAdmissibilityExact as Admissibility
import DASHI.Education.DigitalESDNormativeStandardsAtlasExact as Standards
import DASHI.Education.DigitalESDSourceIntersectionalAuditExact as Intersection
import DASHI.Education.DigitalESDEvidenceBraidTensionExact as Tension
import DASHI.Environment.LESSituatedSocioEcologicalHyperfabricExact as LES

------------------------------------------------------------------------
-- SITUATED SOURCE-AUDIT HYPERFABRIC
--
-- Thin composition only. LES is a structural donor for multi-axis situated
-- reasoning; no LES empirical proposition is imported as Digital-ESD evidence.
------------------------------------------------------------------------

record SourceAuditHyperfabric : Set where
  constructor source-audit-hyperfabric
  field
    source : Attr.AttributedSource
    observations : List Observer.SituatedAuditObservation
    admissibilityFibres : List Admissibility.AdmissibleEvidenceFibre
    standardLenses : List Standards.StandardLens
    intersections : List Intersection.IntersectionReceipt
    tensions : List Tension.TensionReceipt
    scoringProtocolVersion : String
    structuralDonorReading : String

open SourceAuditHyperfabric public

lesStructuralDonorReading : String
lesStructuralDonorReading =
  "LESSituatedSocioEcologicalHyperfabricExact is reused only as a structural precedent for keeping provenance, relation, history and justice coordinates jointly visible. It contributes no empirical Digital-ESD observation by import."

------------------------------------------------------------------------
-- Coarse visibility profile cannot determine full situated audit state.
------------------------------------------------------------------------

data AuditStateWorld : Set where
  sameScoresNoInteraction : AuditStateWorld
  sameScoresInteractionAndTension : AuditStateWorld

data CoarseVisibilityProfile : Set where sameCoarseScores : CoarseVisibilityProfile

data FullAuditState : Set where
  fullStateNoInteraction : FullAuditState
  fullStateInteractionAndTension : FullAuditState

coarseVisibilityProfile : AuditStateWorld → CoarseVisibilityProfile
coarseVisibilityProfile sameScoresNoInteraction = sameCoarseScores
coarseVisibilityProfile sameScoresInteractionAndTension = sameCoarseScores

fullAuditState : AuditStateWorld → FullAuditState
fullAuditState sameScoresNoInteraction = fullStateNoInteraction
fullAuditState sameScoresInteractionAndTension = fullStateInteractionAndTension

fullAuditStatesDiffer :
  fullAuditState sameScoresNoInteraction ≡
  fullAuditState sameScoresInteractionAndTension → ⊥
fullAuditStatesDiffer ()

coarseVisibilityFullStateWitness :
  INF.NonFactorabilityWitness coarseVisibilityProfile fullAuditState
coarseVisibilityFullStateWitness =
  INF.nonFactorabilityWitness
    sameScoresNoInteraction
    sameScoresInteractionAndTension
    refl
    fullAuditStatesDiffer

coarseVisibilityProfileCannotDetermineFullAuditState :
  INF.FactorsThrough coarseVisibilityProfile fullAuditState → ⊥
coarseVisibilityProfileCannotDetermineFullAuditState =
  INF.witnessRulesOutEveryFlatFactorisation coarseVisibilityFullStateWitness

data CoarseVisibilityProfileDeterminesFullAuditState : Set where

data ScoreProfileCreatesEvidenceObject : Set where

data SingleObserverCreatesWholeAuditState : Set where

data StructuralDonorCreatesDomainEvidence : Set where

coarseVisibilityProfileDoesNotDetermineFullAuditState :
  CoarseVisibilityProfileDeterminesFullAuditState → ⊥
coarseVisibilityProfileDoesNotDetermineFullAuditState ()

scoreProfileDoesNotCreateEvidenceObject : ScoreProfileCreatesEvidenceObject → ⊥
scoreProfileDoesNotCreateEvidenceObject ()

singleObserverDoesNotCreateWholeAuditState : SingleObserverCreatesWholeAuditState → ⊥
singleObserverDoesNotCreateWholeAuditState ()

structuralDonorDoesNotCreateDomainEvidence : StructuralDonorCreatesDomainEvidence → ⊥
structuralDonorDoesNotCreateDomainEvidence ()

record SourceAuditHyperfabricBoundary : Set where
  constructor source-audit-hyperfabric-boundary
  field
    scoreIsPrimaryEvidenceObject : Bool
    scoreIsPrimaryEvidenceObjectIsFalse : scoreIsPrimaryEvidenceObject ≡ false
    coarseProfileIsFullAuditState : Bool
    coarseProfileIsFullAuditStateIsFalse : coarseProfileIsFullAuditState ≡ false
    structuralCrossPollinationCreatesEmpiricalAuthority : Bool
    structuralCrossPollinationCreatesEmpiricalAuthorityIsFalse :
      structuralCrossPollinationCreatesEmpiricalAuthority ≡ false
    unresolvedTensionMayRemain : Bool
    unresolvedTensionMayRemainIsTrue : unresolvedTensionMayRemain ≡ true

open SourceAuditHyperfabricBoundary public

canonicalSourceAuditHyperfabricBoundary : SourceAuditHyperfabricBoundary
canonicalSourceAuditHyperfabricBoundary = source-audit-hyperfabric-boundary
  false refl
  false refl
  false refl
  true refl
