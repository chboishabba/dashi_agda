module DASHI.Cognition.PNF.ContextualFractranRegionRestrictionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using (List)

import DASHI.Cognition.PNF.NumericHyperfabric as Region
import DASHI.Cognition.PNF.NumericOccurrenceFibre as Occurrence
import DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact as Context

------------------------------------------------------------------------
-- The existing NumericHyperfabric owns the multiscale region DAG.  This file
-- adds the contravariant/contextual direction: a closed document interface can
-- restrict through selected closed child interfaces to one occurrence without
-- copying immutable child graphs or turning a DB surrogate into semantic id.
------------------------------------------------------------------------

record RegionRestrictionStep : Set where
  constructor regionRestrictionStep
  field
    parent : Region.ClosedInterface
    child : Region.ClosedInterface
    inheritedValuation : Context.ContextualValuation
    childValuation : Context.ContextualValuation

open RegionRestrictionStep public

record RegionRestrictionLadder : Set where
  constructor regionRestrictionLadder
  field
    global : Context.DocumentFractranState
    descent : List RegionRestrictionStep
    occurrence : Occurrence.ScopedTokenOccurrence
    terminalValuation : Context.ContextualValuation

open RegionRestrictionLadder public

record RegionBackwardCompiler : Set₁ where
  constructor regionBackwardCompiler
  field
    restrictStep :
      Region.ClosedInterface →
      Context.ContextualValuation →
      Region.ClosedInterface →
      Context.ContextualValuation

    deriveOccurrence :
      RegionRestrictionLadder →
      Context.WorldId →
      Context.QueryFrame →
      Context.ContextualOccurrenceState

    occurrencePreserved :
      (ladder : RegionRestrictionLadder) →
      (world : Context.WorldId) →
      (query : Context.QueryFrame) →
      Context.occurrence (deriveOccurrence ladder world query)
      ≡ occurrence ladder

open RegionBackwardCompiler public

record RegionRestrictionBoundary : Set where
  constructor regionRestrictionBoundary
  field
    parentCopiesClosedChildInterior : Bool
    restrictionMayUsePromotedKeysAndResidualDemands : Bool
    oneStaticLexicalDictionaryReplacesContextualDescent : Bool
    occurrenceIdentitySurvivesBackwardDescent : Bool

canonicalRegionRestrictionBoundary : RegionRestrictionBoundary
canonicalRegionRestrictionBoundary =
  regionRestrictionBoundary false true false true
