module DASHI.Cognition.CCDCOEP3SituatedHistoryPNFExact where

------------------------------------------------------------------------
-- CCDCOE P3 source-and-history interface for genuinely heterogeneous axes.
--
-- This is NOT a replacement for original formal owners. The actual
-- IntersectionalResidualCarrier retains body/time/place/relation/
-- institution/axis-bundle and EventPNF retains parser/source revision.
-- No fabricated "measured human" or cognitive-war event is constructed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List)
open import Data.Product using (_×_)
open import Data.Empty using (⊥)

import DASHI.Biology.IntersectionalLongitudinalResidualDynamics as Long
import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Cognition.CCDCOEP3TypedIntersectionalAxisExact as Axis
import DASHI.Core.IntersectionalNonFactorability as NF

-- The relationship between a real PNF event, the specified typed
-- coordinates, and a longitudinal situated carrier must be established
-- by the application. The record cannot be constructed merely from a
-- shared demographic count, a Wikipedia label, or a narrative analogy.
record SituatedEventEvidence
  (About : PNF.EventPNF →
           Long.IntersectionalResidualCarrier →
           Axis.Situated → Set) : Set₁ where
  constructor situatedEventEvidence
  field
    originalCandidate : PNF.CandidatePNF
    originalLongitudinalCarrier : Long.IntersectionalResidualCarrier
    originalTypedSituatedState : Axis.Situated
    eventActuallyAboutSituatedState :
      About
        (PNF.event originalCandidate)
        originalLongitudinalCarrier
        originalTypedSituatedState

open SituatedEventEvidence public

-- The original source and history remain accessible, unaltered. This
-- is a well-typed identity projection, not empirical source validity.
originalEvent :
  ∀ {About} → SituatedEventEvidence About → PNF.EventPNF
originalEvent evidence =
  PNF.event (originalCandidate evidence)

sourceRevision :
  ∀ {About} → SituatedEventEvidence About → Nat
sourceRevision evidence =
  PNF.revisionNumber (originalEvent evidence)

originalEventTime :
  ∀ {About} → SituatedEventEvidence About → String
originalEventTime evidence =
  PNF.eventTime (originalEvent evidence)

originalObservationTime :
  ∀ {About} → SituatedEventEvidence About → String
originalObservationTime evidence =
  PNF.observationTime (originalEvent evidence)

longitudinalTime :
  ∀ {About} → SituatedEventEvidence About → Nat
longitudinalTime evidence =
  Long.carrierTime (originalLongitudinalCarrier evidence)

longitudinalAxes :
  ∀ {About} →
  SituatedEventEvidence About → List Long.IntersectionalAxis
longitudinalAxes evidence =
  Long.carrierAxisBundle (originalLongitudinalCarrier evidence)

body : ∀ {About} → SituatedEventEvidence About → String
body evidence = Long.carrierBody (originalLongitudinalCarrier evidence)

place : ∀ {About} → SituatedEventEvidence About → String
place evidence = Long.carrierPlace (originalLongitudinalCarrier evidence)

institution : ∀ {About} → SituatedEventEvidence About → String
institution evidence =
  Long.carrierInstitution (originalLongitudinalCarrier evidence)

relation : ∀ {About} → SituatedEventEvidence About → String
relation evidence =
  Long.carrierRelation (originalLongitudinalCarrier evidence)

-- A source-backed typed coordinate does not automatically describe the
-- entire situated outcome. The actual consumer must request richer
-- evidence and prove the required observation-factorisation.
typedPositionObservation :
  ∀ {About} →
  SituatedEventEvidence About →
  Axis.AxisPoint Axis.raceAxis × Axis.AxisPoint Axis.sexAxis
typedPositionObservation evidence =
  Axis.coordinatesOnly (originalTypedSituatedState evidence)

candidateStatusPreserved :
  ∀ {About} (evidence : SituatedEventEvidence About) →
  PNF.candidateOnly (originalCandidate evidence) ≡ true
candidateStatusPreserved evidence =
  PNF.candidateOnlyIsTrue (originalCandidate evidence)

-- Generic evidence-specific underidentification certificate. The
-- downstream consumer cannot recover a distinction demonstrably
-- erased by its chosen observer, independently of the richness of
-- the evidence that is stored and retained upstream.
sourceIndexedLossCannotBeRecharted :
  ∀ {About : PNF.EventPNF →
                Long.IntersectionalResidualCarrier →
                Axis.Situated → Set}
    {Outcome View : Set}
    (answer : SituatedEventEvidence About → Outcome)
    (rechart :
      (Axis.AxisPoint Axis.raceAxis × Axis.AxisPoint Axis.sexAxis) → View) →
  NF.NonFactorabilityWitness typedPositionObservation answer →
  NF.FactorsThrough
    (λ evidence → rechart (typedPositionObservation evidence))
    answer →
  ⊥
sourceIndexedLossCannotBeRecharted answer rechart witness =
  NF.rechartingCannotRecoverErasedPhenomenon rechart witness
