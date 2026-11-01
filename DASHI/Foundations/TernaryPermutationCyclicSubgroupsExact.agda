module DASHI.Foundations.TernaryPermutationCyclicSubgroupsExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John D. Dixon and Brian Mortimer,
-- "Permutation Groups", Graduate Texts in Mathematics 163,
-- Springer, 1996.
-- DOI: 10.1007/978-1-4612-0731-3.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- Separate the cyclic stabilisers that occur at modular elliptic points from
-- the full ternary permutation group already formalised as S3.
--
-- The existing three-phase carrier receives the cyclic group law C3 and embeds
-- as the rotation subgroup
--
--   {id, r, r^2} < S3.
--
-- The existing two-orientation carrier receives the cyclic group law C2 ~= S2
-- and embeds as
--
--   {id, (low mid)} < S3.
--
-- Both embeddings preserve multiplication exactly and are proper: a
-- transposition is not in the C3 image, and a 3-cycle is not in the chosen C2
-- image.  Thus order-three modular stabiliser data may be related to S3 through
-- an actual subgroup embedding without identifying C3 with the whole S3.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PhaseEnrichedTrit as Phase
import DASHI.Foundations.StageSymmetryCarrierTowerExact as Tower
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Perm
import DASHI.Foundations.TernaryPermutationS3LawsExact as S3

------------------------------------------------------------------------
-- C3 on the existing phase carrier.
------------------------------------------------------------------------

infixl 7 _+₃_

_+₃_ : Phase.Phase3 → Phase.Phase3 → Phase.Phase3
Phase.phase0 +₃ right = right
Phase.phase1 +₃ Phase.phase0 = Phase.phase1
Phase.phase1 +₃ Phase.phase1 = Phase.phase2
Phase.phase1 +₃ Phase.phase2 = Phase.phase0
Phase.phase2 +₃ Phase.phase0 = Phase.phase2
Phase.phase2 +₃ Phase.phase1 = Phase.phase0
Phase.phase2 +₃ Phase.phase2 = Phase.phase1

c3IdentityLeft :
  (phase : Phase.Phase3) →
  Phase.phase0 +₃ phase ≡ phase
c3IdentityLeft Phase.phase0 = refl
c3IdentityLeft Phase.phase1 = refl
c3IdentityLeft Phase.phase2 = refl

c3IdentityRight :
  (phase : Phase.Phase3) →
  phase +₃ Phase.phase0 ≡ phase
c3IdentityRight Phase.phase0 = refl
c3IdentityRight Phase.phase1 = refl
c3IdentityRight Phase.phase2 = refl

c3Associative :
  (a b c : Phase.Phase3) →
  a +₃ (b +₃ c) ≡ (a +₃ b) +₃ c
c3Associative Phase.phase0 Phase.phase0 Phase.phase0 = refl
c3Associative Phase.phase0 Phase.phase0 Phase.phase1 = refl
c3Associative Phase.phase0 Phase.phase0 Phase.phase2 = refl
c3Associative Phase.phase0 Phase.phase1 Phase.phase0 = refl
c3Associative Phase.phase0 Phase.phase1 Phase.phase1 = refl
c3Associative Phase.phase0 Phase.phase1 Phase.phase2 = refl
c3Associative Phase.phase0 Phase.phase2 Phase.phase0 = refl
c3Associative Phase.phase0 Phase.phase2 Phase.phase1 = refl
c3Associative Phase.phase0 Phase.phase2 Phase.phase2 = refl
c3Associative Phase.phase1 Phase.phase0 Phase.phase0 = refl
c3Associative Phase.phase1 Phase.phase0 Phase.phase1 = refl
c3Associative Phase.phase1 Phase.phase0 Phase.phase2 = refl
c3Associative Phase.phase1 Phase.phase1 Phase.phase0 = refl
c3Associative Phase.phase1 Phase.phase1 Phase.phase1 = refl
c3Associative Phase.phase1 Phase.phase1 Phase.phase2 = refl
c3Associative Phase.phase1 Phase.phase2 Phase.phase0 = refl
c3Associative Phase.phase1 Phase.phase2 Phase.phase1 = refl
c3Associative Phase.phase1 Phase.phase2 Phase.phase2 = refl
c3Associative Phase.phase2 Phase.phase0 Phase.phase0 = refl
c3Associative Phase.phase2 Phase.phase0 Phase.phase1 = refl
c3Associative Phase.phase2 Phase.phase0 Phase.phase2 = refl
c3Associative Phase.phase2 Phase.phase1 Phase.phase0 = refl
c3Associative Phase.phase2 Phase.phase1 Phase.phase1 = refl
c3Associative Phase.phase2 Phase.phase1 Phase.phase2 = refl
c3Associative Phase.phase2 Phase.phase2 Phase.phase0 = refl
c3Associative Phase.phase2 Phase.phase2 Phase.phase1 = refl
c3Associative Phase.phase2 Phase.phase2 Phase.phase2 = refl

c3Inverse : Phase.Phase3 → Phase.Phase3
c3Inverse Phase.phase0 = Phase.phase0
c3Inverse Phase.phase1 = Phase.phase2
c3Inverse Phase.phase2 = Phase.phase1

c3InverseLaw :
  (phase : Phase.Phase3) →
  c3Inverse phase +₃ phase ≡ Phase.phase0
c3InverseLaw Phase.phase0 = refl
c3InverseLaw Phase.phase1 = refl
c3InverseLaw Phase.phase2 = refl

embedC3InS3 : Phase.Phase3 → Perm.TriPermutation
embedC3InS3 Phase.phase0 = Perm.permIdentity
embedC3InS3 Phase.phase1 = Perm.permRotate
embedC3InS3 Phase.phase2 = Perm.permRotate2

embedC3Homomorphism :
  (left right : Phase.Phase3) →
  embedC3InS3 (left +₃ right)
  ≡ S3._∙_ (embedC3InS3 left) (embedC3InS3 right)
embedC3Homomorphism Phase.phase0 Phase.phase0 = refl
embedC3Homomorphism Phase.phase0 Phase.phase1 = refl
embedC3Homomorphism Phase.phase0 Phase.phase2 = refl
embedC3Homomorphism Phase.phase1 Phase.phase0 = refl
embedC3Homomorphism Phase.phase1 Phase.phase1 = refl
embedC3Homomorphism Phase.phase1 Phase.phase2 = refl
embedC3Homomorphism Phase.phase2 Phase.phase0 = refl
embedC3Homomorphism Phase.phase2 Phase.phase1 = refl
embedC3Homomorphism Phase.phase2 Phase.phase2 = refl

c3ImageNeverSwapLowMid :
  (phase : Phase.Phase3) →
  embedC3InS3 phase ≡ Perm.permSwapLowMid → ⊥
c3ImageNeverSwapLowMid Phase.phase0 ()
c3ImageNeverSwapLowMid Phase.phase1 ()
c3ImageNeverSwapLowMid Phase.phase2 ()

------------------------------------------------------------------------
-- C2 ~= S2 on the existing orientation carrier.
------------------------------------------------------------------------

infixl 7 _+₂_

_+₂_ : Tower.C2 → Tower.C2 → Tower.C2
Tower.direct +₂ Tower.direct = Tower.direct
Tower.direct +₂ Tower.inverse = Tower.inverse
Tower.inverse +₂ Tower.direct = Tower.inverse
Tower.inverse +₂ Tower.inverse = Tower.direct

c2Associative :
  (a b c : Tower.C2) →
  a +₂ (b +₂ c) ≡ (a +₂ b) +₂ c
c2Associative Tower.direct Tower.direct Tower.direct = refl
c2Associative Tower.direct Tower.direct Tower.inverse = refl
c2Associative Tower.direct Tower.inverse Tower.direct = refl
c2Associative Tower.direct Tower.inverse Tower.inverse = refl
c2Associative Tower.inverse Tower.direct Tower.direct = refl
c2Associative Tower.inverse Tower.direct Tower.inverse = refl
c2Associative Tower.inverse Tower.inverse Tower.direct = refl
c2Associative Tower.inverse Tower.inverse Tower.inverse = refl

embedC2InS3 : Tower.C2 → Perm.TriPermutation
embedC2InS3 Tower.direct = Perm.permIdentity
embedC2InS3 Tower.inverse = Perm.permSwapLowMid

embedC2Homomorphism :
  (left right : Tower.C2) →
  embedC2InS3 (left +₂ right)
  ≡ S3._∙_ (embedC2InS3 left) (embedC2InS3 right)
embedC2Homomorphism Tower.direct Tower.direct = refl
embedC2Homomorphism Tower.direct Tower.inverse = refl
embedC2Homomorphism Tower.inverse Tower.direct = refl
embedC2Homomorphism Tower.inverse Tower.inverse = refl

c2ImageNeverRotate :
  (orientation : Tower.C2) →
  embedC2InS3 orientation ≡ Perm.permRotate → ⊥
c2ImageNeverRotate Tower.direct ()
c2ImageNeverRotate Tower.inverse ()

------------------------------------------------------------------------
-- The StageSymmetry C3 carrier and Phase3 carrier are exactly charted, while
-- their pre-existing rotate operations are also transported.
------------------------------------------------------------------------

phaseToTowerC3 : Phase.Phase3 → Tower.C3
phaseToTowerC3 Phase.phase0 = Tower.negative
phaseToTowerC3 Phase.phase1 = Tower.neutral
phaseToTowerC3 Phase.phase2 = Tower.positive

towerC3ToPhase : Tower.C3 → Phase.Phase3
towerC3ToPhase Tower.negative = Phase.phase0
towerC3ToPhase Tower.neutral = Phase.phase1
towerC3ToPhase Tower.positive = Phase.phase2

phaseTowerRoundTrip :
  (phase : Phase.Phase3) →
  towerC3ToPhase (phaseToTowerC3 phase) ≡ phase
phaseTowerRoundTrip Phase.phase0 = refl
phaseTowerRoundTrip Phase.phase1 = refl
phaseTowerRoundTrip Phase.phase2 = refl

towerPhaseRoundTrip :
  (phase : Tower.C3) →
  phaseToTowerC3 (towerC3ToPhase phase) ≡ phase
towerPhaseRoundTrip Tower.negative = refl
towerPhaseRoundTrip Tower.neutral = refl
towerPhaseRoundTrip Tower.positive = refl

rotationChartCommutes :
  (phase : Phase.Phase3) →
  phaseToTowerC3 (Phase.rotatePhase phase)
  ≡ Tower.rotateC3 (phaseToTowerC3 phase)
rotationChartCommutes Phase.phase0 = refl
rotationChartCommutes Phase.phase1 = refl
rotationChartCommutes Phase.phase2 = refl

record CyclicSubgroupBoundary : Set where
  field
    c3RotationSubgroupConstructed : Bool
    c3RotationSubgroupConstructedIsTrue :
      c3RotationSubgroupConstructed ≡ true
    c2TranspositionSubgroupConstructed : Bool
    c2TranspositionSubgroupConstructedIsTrue :
      c2TranspositionSubgroupConstructed ≡ true
    c3IdentifiedWithWholeS3 : Bool
    c3IdentifiedWithWholeS3IsFalse :
      c3IdentifiedWithWholeS3 ≡ false
    c2IdentifiedWithWholeS3 : Bool
    c2IdentifiedWithWholeS3IsFalse :
      c2IdentifiedWithWholeS3 ≡ false

canonicalCyclicSubgroupBoundary : CyclicSubgroupBoundary
canonicalCyclicSubgroupBoundary = record
  { c3RotationSubgroupConstructed = true
  ; c3RotationSubgroupConstructedIsTrue = refl
  ; c2TranspositionSubgroupConstructed = true
  ; c2TranspositionSubgroupConstructedIsTrue = refl
  ; c3IdentifiedWithWholeS3 = false
  ; c3IdentifiedWithWholeS3IsFalse = refl
  ; c2IdentifiedWithWholeS3 = false
  ; c2IdentifiedWithWholeS3IsFalse = refl
  }
