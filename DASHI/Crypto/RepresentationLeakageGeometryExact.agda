module DASHI.Crypto.RepresentationLeakageGeometryExact where

------------------------------------------------------------------------
-- REPRESENTATION GEOMETRY CAN CHANGE A PHYSICAL OBSERVATION SURFACE
--
-- Same logical transition, same state count, different code-space Hamming
-- movement.  If a physical side channel observes that movement, representation
-- choice changes observation geometry even though semantic information is
-- unchanged.  This is a finite regression only; it asserts no leakage for a
-- named implementation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Crypto.GrayPathTransitionOptimalExact as Gray

record Logical4 : Set where
  constructor logical4
  field
    high low : Bool
open Logical4 public

l0 l1 l2 l3 : Logical4
l0 = logical4 false false
l1 = logical4 false true
l2 = logical4 true false
l3 = logical4 true true

binaryEncode : Logical4 → Gray.Bit2
binaryEncode x = Gray.bit2 (high x) (low x)

-- Gray labelling of logical order 0,1,2,3.
grayEncode : Logical4 → Gray.Bit2
grayEncode (logical4 false false) = Gray.bit2 false false
grayEncode (logical4 false true) = Gray.bit2 false true
grayEncode (logical4 true false) = Gray.bit2 true true
grayEncode (logical4 true true) = Gray.bit2 true false

transitionObservation : (Logical4 → Gray.Bit2) → Logical4 → Logical4 → Nat
transitionObservation encode from to = Gray.hamming2 (encode from) (encode to)

binaryMiddleJump : transitionObservation binaryEncode l1 l2 ≡ 2
binaryMiddleJump = refl

grayMiddleJump : transitionObservation grayEncode l1 l2 ≡ 1
grayMiddleJump = refl

sameLogicalTransitionDifferentPhysicalObservation :
  transitionObservation binaryEncode l1 l2 ≡ 2
  × transitionObservation grayEncode l1 l2 ≡ 1
sameLogicalTransitionDifferentPhysicalObservation = refl , refl
  where
  open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Boundary: smaller code-space movement may be computationally convenient, but
-- it is not automatically a side-channel improvement.  Physical leakage must
-- be modelled and measured separately.
------------------------------------------------------------------------

data LeakageInterpretation : Set where
  representationChangesObservationGeometry : LeakageInterpretation

representationLeakageBoundary : LeakageInterpretation
representationLeakageBoundary = representationChangesObservationGeometry
