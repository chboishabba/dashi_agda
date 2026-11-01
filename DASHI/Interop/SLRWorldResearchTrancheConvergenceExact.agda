module DASHI.Interop.SLRWorldResearchTrancheConvergenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRSemanticWorldClosureExact as Closure

------------------------------------------------------------------------
-- JOINED GWB / AU / BREXIT WORLD-RESEARCH TRANCHE ABI
------------------------------------------------------------------------

data TrancheReadiness : Set where
  worldReady : TrancheReadiness
  retainedSourceReady : TrancheReadiness
  sourceUnpaid : TrancheReadiness

record WorldResearchTranche : Set where
  constructor worldResearchTranche
  field
    trancheReference : String
    readiness : TrancheReadiness
    evidenceReference : String
    mayContributeSemanticAtoms : Bool
    nextObligationReference : String
    candidateOnly : Bool
    semanticPromotion : Bool

open WorldResearchTranche public

canonicalTranches : List WorldResearchTranche
canonicalTranches =
  worldResearchTranche
    "gwb"
    worldReady
    "10 docs / 41,134 sentences / CandidateWorldModel + reviewed Wikimedia graph"
    true
    "consumer-specific semantic gap contraction"
    true false
  ∷ worldResearchTranche
    "au"
    retainedSourceReady
    "45 retained documents / 19,235 sentences / execution parity paid"
    false
    "project retained AU sources into generic CandidateWorldModel/world-research iteration"
    true false
  ∷ worldResearchTranche
    "brexit"
    sourceUnpaid
    "structured intent fixture only; no retained narrative/source certification"
    false
    "acquire retained narrative/source material before semantic closure"
    true false
  ∷ []

record WorldResearchIterationBoundary : Set where
  constructor worldResearchIterationBoundary
  field
    worldReadyMayContributeAtoms : Bool
    retainedSourceReadyMayContributeAtomsBeforeProjection : Bool
    sourceUnpaidMayContributeAtoms : Bool
    semanticGapsDriveNextAcquisition : Bool
    wikimediaBeforeBroadSnowball : Bool
    propagatedEvidenceRewritesSource : Bool
    iterationAppendOnly : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open WorldResearchIterationBoundary public

canonicalWorldResearchIterationBoundary : WorldResearchIterationBoundary
canonicalWorldResearchIterationBoundary =
  worldResearchIterationBoundary true false false true true false true true false

semanticClosureAnchor : Closure.SemanticClosureBoundary
semanticClosureAnchor = Closure.canonicalSemanticClosureBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SourceUnpaidContributesSemanticAtoms : Set where
data RetainedSourceExecutionParityEqualsWorldReadiness : Set where
data TrancheReadinessCreatesTruth : Set where
data GapMaySkipWikimediaAndJumpToBroadSnowball : Set where

sourceUnpaidCannotContributeSemanticAtoms : SourceUnpaidContributesSemanticAtoms → ⊥
sourceUnpaidCannotContributeSemanticAtoms ()

executionParityDoesNotEqualWorldReadiness : RetainedSourceExecutionParityEqualsWorldReadiness → ⊥
executionParityDoesNotEqualWorldReadiness ()

trancheReadinessDoesNotCreateTruth : TrancheReadinessCreatesTruth → ⊥
trancheReadinessDoesNotCreateTruth ()

gapMustRespectWikimediaFirstRouting : GapMaySkipWikimediaAndJumpToBroadSnowball → ⊥
gapMustRespectWikimediaFirstRouting ()
