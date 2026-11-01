module DASHI.Crypto.BlueTeamThreatModelExact where

------------------------------------------------------------------------
-- COMPOSED BLUE-TEAM THREAT MODEL
--
-- One theorem-bearing surface connecting public projection, active observation,
-- protected output, finite candidate masks and per-query cost.  Adapters reuse
-- the Round-16 observation and protected-label cores rather than duplicating
-- their proofs.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_)

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
    initialCandidateMask : List Bool

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
    labelLeft labelRight : Hidden model
    labelSamePublic : project model labelLeft ≡ project model labelRight
    labelsDiffer : protected model labelLeft ≡ protected model labelRight → ⊥

open PublicProtectedLabelSplit public

asTranscriptLabelSplit :
  ∀ {model : BlueTeamThreatModel} →
  PublicProtectedLabelSplit model →
  Label.TranscriptLabelFibreSplit (asPublicLabelSystem model)
asTranscriptLabelSplit split =
  Label.transcriptLabelFibreSplit
    (labelLeft split)
    (labelRight split)
    (labelSamePublic split)
    (labelsDiffer split)

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
    obsLeft obsRight : Hidden model
    obsSamePublic : project model obsLeft ≡ project model obsRight
    obsQuery : Query model
    obsDiffers : observe model obsLeft obsQuery ≡ observe model obsRight obsQuery → ⊥

open ThreatObservationSplit public

asHiddenDependentSplit :
  ∀ {model : BlueTeamThreatModel} →
  ThreatObservationSplit model →
  Observation.HiddenDependentSplit (asObservationSystem model)
asHiddenDependentSplit split =
  Observation.hiddenDependentSplit
    (obsLeft split)
    (obsRight split)
    (obsSamePublic split)
    (obsQuery split)
    (obsDiffers split)

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
  Fibre.liveCount (afterMask refinement) ≤
  Fibre.liveCount (initialCandidateMask model)
candidateRefinementCannotIncrease refinement =
  Fibre.refinementCannotIncreaseCardinality (refines refinement)
