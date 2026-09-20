module DASHI.Physics.Closure.NSTriadKNR571OppositeShiftMidpointObstructionExact where

------------------------------------------------------------------------
-- PERIODIC B / OPPOSITE-SHIFT MIDPOINT NECESSITY
--
-- The preferred R571 second-moment carrier is genuinely centered:
--
--   plus  = center + y
--   minus = center - y.
--
-- Therefore any literal pair represented by that carrier necessarily satisfies
--
--   plus + minus = 2 center.
--
-- An arbitrary physical inner incidence a+b=p does NOT supply such a center
-- automatically.  This owner records the exact same-object necessity so the
-- live R567/R573 homochiral carrier cannot be silently coerced into the
-- opposite-shift Taylor carrier when p has no integral midpoint.
--
-- This is an obstruction/typing theorem, not a failure of the radial estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNIntegerFourierModeAddExact as Add
import DASHI.Physics.Closure.NSTriadKNR571OppositeShiftPairedCommutatorExact as Opp
import DASHI.Physics.Closure.NSTriadKNR571CenteredShiftTriangleExcessExact as Centered

record OppositeShiftRepresentation
    (plus minus : Z3.FourierMode) : Set where
  constructor opposite-shift-representation
  field
    center displacement : Z3.FourierMode
    plusMeaning : plus ≡ Opp.plusMode center displacement
    minusMeaning : minus ≡ Opp.minusMode center displacement

open OppositeShiftRepresentation public

oppositeShiftPairHasDoubledCenterSum :
  ∀ {plus minus} →
  (R : OppositeShiftRepresentation plus minus) →
  Z3.addMode plus minus ≡ Centered.doubledCenter (center R)
oppositeShiftPairHasDoubledCenterSum R =
  trans
    (cong₂ Z3.addMode (plusMeaning R) (minusMeaning R))
    (Centered.centeredShiftSumIsDoubledCenter
      (center R) (displacement R))

record PhysicalPairMidpointCompatibility
    (a b output : Z3.FourierMode) : Set where
  constructor physical-pair-midpoint-compatibility
  field
    resonance : Z3.addMode a b ≡ output
    centered : OppositeShiftRepresentation a b

open PhysicalPairMidpointCompatibility public

physicalPairOppositeShiftForcesDoubledOutput :
  ∀ {a b output} →
  (C : PhysicalPairMidpointCompatibility a b output) →
  output ≡ Centered.doubledCenter (center (centered C))
physicalPairOppositeShiftForcesDoubledOutput C =
  trans
    (sym (resonance C))
    (oppositeShiftPairHasDoubledCenterSum (centered C))

oppositeShiftMidpointNecessityClosed : Bool
oppositeShiftMidpointNecessityClosed = true

arbitraryPhysicalInnerPairAutomaticallyHasIntegralMidpoint : Bool
arbitraryPhysicalInnerPairAutomaticallyHasIntegralMidpoint = false

homochiralR573CanBeGloballyCoercedToOppositeShiftByFiat : Bool
homochiralR573CanBeGloballyCoercedToOppositeShiftByFiat = false

nextValidRoutesAreParitySplitOrNoncenteredCompiler : Bool
nextValidRoutesAreParitySplitOrNoncenteredCompiler = true

clayPromotion : Bool
clayPromotion = false

oppositeShiftMidpointNecessityClosedIsTrue :
  oppositeShiftMidpointNecessityClosed ≡ true
oppositeShiftMidpointNecessityClosedIsTrue = refl

arbitraryPhysicalInnerPairAutomaticallyHasIntegralMidpointIsFalse :
  arbitraryPhysicalInnerPairAutomaticallyHasIntegralMidpoint ≡ false
arbitraryPhysicalInnerPairAutomaticallyHasIntegralMidpointIsFalse = refl
