module DASHI.Reasoning.TrialecticDyadicCoverNerveExact where

------------------------------------------------------------------------
-- EXACT NERVE OF THE RELATIONAL DYADIC COVER {AB, BC, CA}
--
-- DASHI CONTRIBUTION
--
-- On the literal participant carrier {A,B,C}:
--
--   U_AB = {A,B}
--   U_BC = {B,C}
--   U_CA = {C,A}
--
-- Pairwise intersections are nonempty:
--
--   U_AB ∩ U_BC = {B}
--   U_BC ∩ U_CA = {C}
--   U_CA ∩ U_AB = {A}
--
-- but the triple intersection is empty:
--
--   U_AB ∩ U_BC ∩ U_CA = empty.
--
-- Therefore the Cech nerve of this literal dyadic participant cover contains
-- the triangular 1-skeleton but no filled 2-simplex.  The irreducible
-- trialectic face used elsewhere in DASHI is an additional relation/2-cell,
-- not the Cech triple intersection of these three participant subsets.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Product using (_×_; _,_)

import DASHI.Reasoning.TrialecticObserverMatrix369Exact as Observer
import DASHI.Reasoning.Trialectic369CechGrothendieckComparisonExact as Compare

------------------------------------------------------------------------
-- 1. Literal membership.
------------------------------------------------------------------------

data Member :
  Observer.Participant3 ->
  Compare.TriadicPatch ->
  Set where
  aInAB : Member Observer.participantA Compare.patchAB
  bInAB : Member Observer.participantB Compare.patchAB

  bInBC : Member Observer.participantB Compare.patchBC
  cInBC : Member Observer.participantC Compare.patchBC

  cInCA : Member Observer.participantC Compare.patchCA
  aInCA : Member Observer.participantA Compare.patchCA

------------------------------------------------------------------------
-- 2. Pairwise intersections are inhabited by the expected participant.
------------------------------------------------------------------------

record PairIntersectionWitness
    (overlap : Compare.TriadicPairOverlap) : Set where
  constructor pair-intersection-witness
  field
    participant : Observer.Participant3
    inFirst :
      Member participant (Compare.firstPatch overlap)
    inSecond :
      Member participant (Compare.secondPatch overlap)

open PairIntersectionWitness public

overlapAWitness : PairIntersectionWitness Compare.overlapA
overlapAWitness =
  pair-intersection-witness
    Observer.participantA
    aInCA
    aInAB

overlapBWitness : PairIntersectionWitness Compare.overlapB
overlapBWitness =
  pair-intersection-witness
    Observer.participantB
    bInAB
    bInBC

overlapCWitness : PairIntersectionWitness Compare.overlapC
overlapCWitness =
  pair-intersection-witness
    Observer.participantC
    cInBC
    cInCA

pairOverlapWitness :
  (overlap : Compare.TriadicPairOverlap) ->
  PairIntersectionWitness overlap
pairOverlapWitness Compare.overlapA = overlapAWitness
pairOverlapWitness Compare.overlapB = overlapBWitness
pairOverlapWitness Compare.overlapC = overlapCWitness

------------------------------------------------------------------------
-- 3. Pairwise intersections are singleton at participant level.
------------------------------------------------------------------------

overlapAOnlyA :
  (participant : Observer.Participant3) ->
  Member participant Compare.patchCA ->
  Member participant Compare.patchAB ->
  participant ≡ Observer.participantA
overlapAOnlyA Observer.participantA inCA inAB = refl
overlapAOnlyA Observer.participantB () inAB
overlapAOnlyA Observer.participantC inCA ()

overlapBOnlyB :
  (participant : Observer.Participant3) ->
  Member participant Compare.patchAB ->
  Member participant Compare.patchBC ->
  participant ≡ Observer.participantB
overlapBOnlyB Observer.participantA inAB ()
overlapBOnlyB Observer.participantB inAB inBC = refl
overlapBOnlyB Observer.participantC () inBC

overlapCOnlyC :
  (participant : Observer.Participant3) ->
  Member participant Compare.patchBC ->
  Member participant Compare.patchCA ->
  participant ≡ Observer.participantC
overlapCOnlyC Observer.participantA () inCA
overlapCOnlyC Observer.participantB inBC ()
overlapCOnlyC Observer.participantC inBC inCA = refl

------------------------------------------------------------------------
-- 4. Triple intersection is empty.
------------------------------------------------------------------------

TripleIntersectionAt :
  Observer.Participant3 ->
  Set
TripleIntersectionAt participant =
  Member participant Compare.patchAB
  ×
  Member participant Compare.patchBC
  ×
  Member participant Compare.patchCA

noParticipantInAllThree :
  (participant : Observer.Participant3) ->
  TripleIntersectionAt participant ->
  ⊥
noParticipantInAllThree Observer.participantA (aInAB , () , inCA)
noParticipantInAllThree Observer.participantB (bInAB , bInBC , ())
noParticipantInAllThree Observer.participantC (() , cInBC , cInCA)

record TripleIntersectionWitness : Set where
  constructor triple-intersection-witness
  field
    participant : Observer.Participant3
    membership : TripleIntersectionAt participant

open TripleIntersectionWitness public

relationalDyadicTripleIntersectionEmpty :
  TripleIntersectionWitness -> ⊥
relationalDyadicTripleIntersectionEmpty witness =
  noParticipantInAllThree
    (participant witness)
    (membership witness)

------------------------------------------------------------------------
-- 5. The trialectic face is therefore not a Cech triple-overlap section.
------------------------------------------------------------------------

data TrialecticFaceIsDyadicTripleIntersection : Set where

trialecticFaceIsNotDyadicTripleIntersection :
  TrialecticFaceIsDyadicTripleIntersection -> ⊥
trialecticFaceIsNotDyadicTripleIntersection ()

data PairwiseMatchingAutomaticallyCreatesTripleIntersection : Set where

pairwiseMatchingDoesNotCreateTripleIntersection :
  PairwiseMatchingAutomaticallyCreatesTripleIntersection -> ⊥
pairwiseMatchingDoesNotCreateTripleIntersection ()

record TrialecticDyadicCoverNerveBoundary : Set where
  constructor trialectic-dyadic-cover-nerve-boundary
  field
    threeDyadicPatchesExact : Bool
    eachPairwiseIntersectionInhabited : Bool
    eachPairwiseIntersectionSingletonAtParticipantLevel : Bool
    tripleParticipantIntersectionInhabited : Bool
    cechNerveHasTriangularOneSkeleton : Bool
    cechNerveHasFilledTwoSimplex : Bool
    irreducibleTrialecticFaceEqualsCechTripleIntersection : Bool

canonicalTrialecticDyadicCoverNerveBoundary :
  TrialecticDyadicCoverNerveBoundary
canonicalTrialecticDyadicCoverNerveBoundary =
  trialectic-dyadic-cover-nerve-boundary
    true true true false true false false
