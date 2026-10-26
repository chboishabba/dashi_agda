module DASHI.Mathematics.Topology.ExoticHornChronologicalCantorConsumerExact where

------------------------------------------------------------------------
-- REAL CROSS-PR PROOF JOIN, NO DUPLICATE CODEC
--
-- Existing horn owner (Alexander PR #1244):
--   AlexanderHornedC3ChronologicalClopenBridgeExact:
--     source-owned chronologicalCylinder, append proofs,
--     C3 rotation unchanged on cylinder coordinates.
-- Existing child owner (exotic topology PR #1254):
--   ExoticCantorCylinderOrientationExact:
--     actual chronological stream-cylinder membership,
--     all-prefix APPEND-child event inclusion theorem.
-- Canonical Cantor owner (unchanged):
--   CantorProjectiveCylinderMeasureExact.BitStream/Cylinder.
--
-- FINITE SYMBOLIC / ENDPOINT-EVENT statement:
-- The original newest-first Horn.leftChild and rightChild
-- select subsets of the SAME chronological stream cylinder,
-- after the original horn chronology conversion.
--
-- C3 permutes the three external sectors without changing any
-- endpoint bit stream. No assertion of a continuous map from a
-- connected wild exterior E into a nontrivial Cantor endpoint set,
-- ambient R3 wildness, genuine pi1 or Borel measure extension.
--
-- Historical: Alexander 1924, Hatcher Example 2B.2;
-- repository-local first formal horn/stream conversion owned
-- by #1244, this proof consumer is #1254.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Nat using (zero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Foundations.CantorProjectiveCylinderMeasureExact as Cantor
import DASHI.Mathematics.Topology.AlexanderHornedC3FiniteStageExact as Horn
import DASHI.Mathematics.Topology.AlexanderHornedC3ChronologicalClopenBridgeExact as OriginalHorn
import DASHI.Mathematics.Topology.ExoticCantorCylinderOrientationExact as Event

hornLeftChronologicalCylinderRefines :
  (h : Horn.HornAddress) (stream : Cantor.BitStream) →
  Event.Matches (OriginalHorn.chronologicalCylinder (Horn.leftChild h)) stream →
  Event.Matches (OriginalHorn.chronologicalCylinder h) stream
hornLeftChronologicalCylinderRefines h stream proof =
  Event.appendChildRefinesAt
    zero (Cantor.prefix (OriginalHorn.chronologicalCylinder h))
    false stream
    (subst
      (λ bits → Event.MatchesAt zero bits stream)
      (OriginalHorn.leftChildAppendsChronologicalBit h)
      proof)

hornRightChronologicalCylinderRefines :
  (h : Horn.HornAddress) (stream : Cantor.BitStream) →
  Event.Matches (OriginalHorn.chronologicalCylinder (Horn.rightChild h)) stream →
  Event.Matches (OriginalHorn.chronologicalCylinder h) stream
hornRightChronologicalCylinderRefines h stream proof =
  Event.appendChildRefinesAt
    zero (Cantor.prefix (OriginalHorn.chronologicalCylinder h))
    true stream
    (subst
      (λ bits → Event.MatchesAt zero bits stream)
      (OriginalHorn.rightChildAppendsChronologicalBit h)
      proof)

hornRotationPreservesChronologicalMembership :
  (h : Horn.HornAddress) (stream : Cantor.BitStream) →
  Event.Matches (OriginalHorn.chronologicalCylinder h) stream →
  Event.Matches
    (OriginalHorn.chronologicalCylinder (Horn.rotateAddress h))
    stream
hornRotationPreservesChronologicalMembership h stream proof
  rewrite OriginalHorn.rotationPreservesChronologicalCylinder h = proof

-- The two source-owned prefix orientations are reconciled for the
-- horn END-CYLINDER events. Existing Cantor.leftChild still
-- prepends a stack bit and its MASS identity remains a separate
-- theorem: no false claim about ambient clopen exterior sectors.
