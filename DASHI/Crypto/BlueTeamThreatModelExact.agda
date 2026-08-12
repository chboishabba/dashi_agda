module DASHI.Crypto.BlueTeamThreatModelExact where

------------------------------------------------------------------------
-- COMPOSED BLUE-TEAM THREAT MODEL
--
-- One theorem-bearing surface connecting public projection, active observation,
-- protected output, finite candidate masks and per-query cost.  Adapters reuse
-- the Round-16 observation and protected-label cores rather than duplicating
-- their proofs.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Crypto.BlueTeamAdversaryObservationExact as Observation
import DASHI.Crypto.TranscriptProtectedLabelExact as Label
import DASHI.Crypto.FiniteCandidateFibreCardinalityExact as Fibre

record BlueTeamThreatModel : Set₁ where
  constructor blueTeamThreatModel
  field
    Hidden Public Query ObservationValue ProtectedLabel : Set
    project : Hidden → Public
    observe : Hidden → Query → ObservationValue
    protected : Hidden → ProtectedLabel
    queryCost : Query → Nat
    initialCandidateMask : List Agda.Builtin.Bool.Bool

open import Agda.Builtin.Bool
open BlueTeamThreatModel public

asObservationSystem : BlueTeamThreatModel → Observation.BlueTeamAdversarySystem
asObservationSystem model =
  Observation.blueTeamAdversarySystem
    (Hidden model)
    (Public model)
    (Query model)
    (ObservationValue model)
    (project model)
    (observe model)

asPublicLabelSystem : BlueTeamThreatModel → Label.TranscriptLabelSystem
asPublicLabelSystem model =
  Label.transcriptLabelSystem
    (Hidden model)
    (Public model)
    (ProtectedLabel model)
    (project model)
    (protected model)

record PublicProtectedLabelSplit (model : BlueTeamThreatModel) : Set where
  constructor publicProtectedLabelSplit
  field
    left right : Hidden model
    samePublic : project model left ≡ project model right
    labelsDiffer : protected model left ≡ protected model right → ⊥

open PublicProtectedLabelSplit public

asTranscriptLabelSplit :
  ∀ {model : BlueTeamThreatModel} →
  PublicProtectedLabelSplit model →
  Label.TranscriptLabelFibreSplit (asPublicLabelSystem model)
asTranscriptLabelSplit split =
  Label.transcriptLabelFibreSplit
    (left split) (right split) (samePublic split) (labelsDiffer split)

publicProtectedLabelSplitRefutesExactRecovery :
  ∀ {model : BlueTeamThreatModel} →
  PublicProtectedLabelSplit model →
  Label.ExactTranscriptLabelRecovery (asPublicLabelSystem model) → ⊥
publicProtectedLabelSplitRefutesExactRecovery split =
  Label.transcriptLabelSplitRefutesExactRecovery (asTranscriptLabelSplit split)

record PublicFactoredObservation (model : BlueTeamThreatModel) : Set₁ where
  constructor publicFactoredObservation
  field
    answer : Public model → Query model → ObservationValue model
    factors : ∀ hidden q →
      observe model hidden q ≡ answer (project model hidden) q

open PublicFactoredObservation public

asPublicFactored :
  ∀ {model : BlueTeamThreatModel} →
  PublicFactoredObservation model →
  Observation.PublicFactored (asObservationSystem model)
asPublicFactored factored =
  Observation.publicFactored (answer factored) (factors factored)

record ThreatObservationSplit (model : BlueTeamThreatModel) : Set where
  constructor threatObservationSplit
  field
    left right : Hidden model
    samePublic : project model left ≡ project model right
    query : Query model
    differs : observe model left query ≡ observe model right query → ⊥

open ThreatObservationSplit public

asHiddenDependentSplit :
  ∀ {model : BlueTeamThreatModel} →
  ThreatObservationSplit model →
  Observation.HiddenDependentSplit (asObservationSystem model)
asHiddenDependentSplit split =
  Observation.hiddenDependentSplit
    (left split) (right split) (samePublic split) (query split) (differs split)

publicFactoredThreatObservationCannotSplit :
  ∀ {model : BlueTeamThreatModel} →
  PublicFactoredObservation model →
  ThreatObservationSplit model → ⊥
publicFactoredThreatObservationCannotSplit factored split =
  Observation.publicFactoredCannotSplitSamePublicFibre
    (asPublicFactored factored)
    (asHiddenDependentSplit split)

record CandidateRefinement (model : BlueTeamThreatModel) : Set where
  constructor candidateRefinement
  field
    afterMask : List Bool
    refines : Fibre.Refines (initialCandidateMask model) afterMask

open CandidateRefinement public

candidateRefinementCannotIncrease :
  ∀ {model : BlueTeamThreatModel}
    (refinement : CandidateRefinement model) →
  Fibre.liveCount (afterMask refinement)
  Data.Nat.Base.≤
  Fibre.liveCount (initialCandidateMask model)
candidateRefinementCannotIncrease refinement =
  Fibre.refinementCannotIncreaseCardinality (refines refinement)
  where
  import Data.Nat.Base
