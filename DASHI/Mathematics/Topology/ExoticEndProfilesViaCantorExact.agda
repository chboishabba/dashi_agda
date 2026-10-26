module DASHI.Mathematics.Topology.ExoticEndProfilesViaCantorExact where

------------------------------------------------------------------------
-- SOURCE / PROVENANCE
-- Ian Richards, "On the Classification of Noncompact Surfaces" (1963).
-- Richards classifies actual noncompact surfaces using genus, orientability,
-- end spaces and ends accumulated by genus.
-- Existing DASHI owner:
-- DASHI.Foundations.CantorProjectiveCylinderMeasureExact.
--
-- This module is an EXACT combinatorial presentation of THREE proposed
-- end/genus profiles. It does NOT construct surfaces, their topologies,
-- collars, or the equivalence between these profiles and actual ends.
-- That geometric-realisation obligation must be discharged separately.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (_+_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Foundations.CantorProjectiveCylinderMeasureExact as Cantor
import DASHI.Mathematics.Topology.ExoticCantorCylinderOrientationExact as Order

data Unit : Set where
  unit : Unit

data SurfaceProfile : Set where
  cantorTree lochNessMonster jacobsLadder : SurfaceProfile

-- Pure end CODES. Neither these nor the assigned genus markers imply
-- topological classification before a concrete surface realisation.
EndCode : SurfaceProfile → Set
EndCode cantorTree = Cantor.BitStream
EndCode lochNessMonster = Unit
EndCode jacobsLadder = Bool

leftCantorEnd rightCantorEnd : EndCode cantorTree
leftCantorEnd  n = false
rightCantorEnd n = true

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

cantorEndCodesDistinct : leftCantorEnd ≡ rightCantorEnd → ⊥
cantorEndCodesDistinct equality =
  falseNotTrue (cong (λ stream → stream zero) equality)

jacobEndCodesDistinct : (false ≡ true) → ⊥
jacobEndCodesDistinct = falseNotTrue

-- Handle occurrence schedules at each depth, not geometric handles.
hasMarkedHandle : (family : SurfaceProfile) → EndCode family → Nat → Bool
hasMarkedHandle cantorTree        end depth = false
hasMarkedHandle lochNessMonster   end depth = true
hasMarkedHandle jacobsLadder      end depth = true

cantorTreePlanarCode :
  (end : EndCode cantorTree) (depth : Nat) →
  hasMarkedHandle cantorTree end depth ≡ false
cantorTreePlanarCode end depth = refl

lochNessHasUnboundedHandleSchedule :
  (end : EndCode lochNessMonster) (depth : Nat) →
  hasMarkedHandle lochNessMonster end (suc depth) ≡ true
lochNessHasUnboundedHandleSchedule end depth = refl

jacobsLadderBothEndsHandleSchedule :
  (end : EndCode jacobsLadder) (depth : Nat) →
  hasMarkedHandle jacobsLadder end (suc depth) ≡ true
jacobsLadderBothEndsHandleSchedule end depth = refl

-- Reuse the ORIGINAL dyadic premeasure theorem; no duplicate Cantor
-- cylinder mass or fabricated topological clopen-set proof.
cantorEndCylinderMassRefines :
  (c : Cantor.Cylinder) →
  Cantor.cylinderMass (Cantor.leftChild c)
    + Cantor.cylinderMass (Cantor.rightChild c)
    ≡ Cantor.cylinderMass c
cantorEndCylinderMassRefines = Cantor.parentMassSplitsExactly

------------------------------------------------------------------------
-- REAL EVENT REFINEMENT ON THE EXISTING END-CODE CARRIER
--
-- The canonical source Cantor.leftChild PREPENDS a stack bit.
-- It splits the length-only dyadic mass but is not chronological
-- inclusion for the underlying stream event. Reuse the corrected,
-- proof-bearing APPEND-child interpretation without replacing
-- the source's premeasure, and block its false promotion explicitly.
------------------------------------------------------------------------

cantorEndLeftChronologicalRefines :
  (event : Cantor.Cylinder) (stream : EndCode cantorTree) →
  Order.Matches (Order.appendLeft event) stream →
  Order.Matches event stream
cantorEndLeftChronologicalRefines = Order.appendLeftRefines

cantorEndRightChronologicalRefines :
  (event : Cantor.Cylinder) (stream : EndCode cantorTree) →
  Order.Matches (Order.appendRight event) stream →
  Order.Matches event stream
cantorEndRightChronologicalRefines = Order.appendRightRefines

cantorOriginalStackChildIsNotChronologicalInclusion :
  ((stream : EndCode cantorTree) →
   Order.Matches (Cantor.leftChild Order.sampleParent) stream →
   Order.Matches Order.sampleParent stream) → ⊥
cantorOriginalStackChildIsNotChronologicalInclusion =
  Order.oldPrependIsNotChronologicalRefinement

-- This is a schedule-level semantic difference, NOT a homeomorphism
-- obstruction on its own without a realised surface and its end map.
cantorCannotAcquireScheduledHandle :
  (end : EndCode cantorTree) (depth : Nat) →
  hasMarkedHandle cantorTree end depth ≡ true → ⊥
cantorCannotAcquireScheduledHandle end depth ()
