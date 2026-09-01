module DASHI.Cognition.PNF.CrossStratumIdentityFractranFibreExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List)

import DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact as Context
import DASHI.Cognition.PNF.BracketedTSFVFractranWorldFibreExact as World

------------------------------------------------------------------------
-- Identity/persona hypotheses may be tested in radically different strata
-- (performance, domestic, interview, social, etc.).  A coherent identity is a
-- section through those changing contextual fibres; it is not one static prime.
------------------------------------------------------------------------

data IdentityHypothesis : Set where
  identityHypothesis : Nat → IdentityHypothesis

data ContextStratumKind : Set where
  performanceStratum domesticStratum interviewStratum socialStratum : ContextStratumKind
  genericStratum : Nat → ContextStratumKind

record SituatedIdentityEvidence : Set where
  constructor situatedIdentityEvidence
  field
    hypothesis : IdentityHypothesis
    stratumKind : ContextStratumKind
    world : World.WorldHistory
    valuation : Context.ContextualValuation
    confirmatory : Bool
    salientResidual : Bool

open SituatedIdentityEvidence public

record CrossStratumIdentitySection : Set where
  constructor crossStratumIdentitySection
  field
    persistentHypothesis : IdentityHypothesis
    observations : List SituatedIdentityEvidence

open CrossStratumIdentitySection public

------------------------------------------------------------------------
-- Near-match/uncanny states are represented by strong confirmatory projection
-- together with an undisclosed salient residual.  No psychological theorem is
-- asserted; this is the fibre shape needed to retain near-equivalence without
-- collapsing identity.
------------------------------------------------------------------------

record NearIdentityResidual : Set where
  constructor nearIdentityResidual
  field
    evidence : SituatedIdentityEvidence
    projectedMatch : Bool
    residualRemains : Bool

open NearIdentityResidual public

record IdentityFibreBoundary : Set where
  constructor identityFibreBoundary
  field
    lexicalNameHasOneIdentityPrime : Bool
    sameAppearanceProjectionMeansSameIdentity : Bool
    identityMayRemainCoherentAcrossDifferentStrata : Bool
    highProjectedMatchMayRetainSalientResidual : Bool
    personaCompatibilityIsHistoricalFactAuthority : Bool

canonicalIdentityFibreBoundary : IdentityFibreBoundary
canonicalIdentityFibreBoundary =
  identityFibreBoundary false false true true false
