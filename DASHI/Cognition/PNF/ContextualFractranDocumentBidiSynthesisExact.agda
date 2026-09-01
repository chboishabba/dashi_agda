module DASHI.Cognition.PNF.ContextualFractranDocumentBidiSynthesisExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List)

import DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact as Context
import DASHI.Cognition.PNF.BracketedTSFVFractranWorldFibreExact as World
import DASHI.Cognition.PNF.ConsumerRelationSheetFractranQuotientBidiExact as Relation
import DASHI.Cognition.PNF.SelfIndexedSemanticFractranTetrationBidiExact as Tower
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed

------------------------------------------------------------------------
-- One synthesis object for the thread-wide architecture.
-- Forward direction: parser occurrences -> candidate worlds -> contextual
-- valuations -> requested observations.
-- Backward direction: closed document state -> world -> occurrence restriction.
------------------------------------------------------------------------

record ContextualFractranDocumentBidi : Set₁ where
  constructor contextualFractranDocumentBidi
  field
    document : Context.DocumentFractranState
    multiverse : World.TSFVMultiverse
    backwardLaw : Context.BackwardDerivationLaw

    requestedPrime : Signed.SSPPrime
    relationSheet : Relation.RelationSheet3

    -- Optional semantic self-indexing level supplied by a consumer that really
    -- uses the whole prior carrier as the next index set.
    TetrationLevel : Set

open ContextualFractranDocumentBidi public

record BidiArchitectureBoundary : Set where
  constructor bidiArchitectureBoundary
  field
    wordPOSStaticDictionaryIsContextualValuation : Bool
    parserObservationIsWorldAuthority : Bool
    queryProjectionMayRetainManyWorlds : Bool
    bracketControlsWhenAvailableOptionCanExecute : Bool
    reciprocalFractionCanRepresentCandidateInverse : Bool
    candidateInverseAlwaysLawful : Bool
    selfIndexingCanUseExistingNineTetration : Bool
    ordinaryProductGrowthEqualsTetration : Bool

canonicalBidiArchitectureBoundary : BidiArchitectureBoundary
canonicalBidiArchitectureBoundary =
  bidiArchitectureBoundary
    false false true true true false true false
