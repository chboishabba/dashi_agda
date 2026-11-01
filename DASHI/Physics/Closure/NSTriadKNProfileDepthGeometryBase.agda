module DASHI.Physics.Closure.NSTriadKNProfileDepthGeometryBase where

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_; _+_)

------------------------------------------------------------------------
-- Shared Blocker 1 profile-depth geometry base.
--
-- This isolates the depth-bearing profile labels from the downstream
-- weight/refinement files so they can be used definitionally without
-- creating import cycles.
------------------------------------------------------------------------

postulate
  entryDepth : Nat → Nat
  maxDepth : Nat
  entryDepthBound : (k : Nat) → entryDepth k ≤ maxDepth
  forcedTailSourceDepthCap : Nat → Nat

advLogDepthRequired : Nat → Nat
advLogDepthRequired N = N

transLogDepthRequired : Nat → Nat
transLogDepthRequired N = N

record ForcedTailSourceDef (N i : Nat) : Set where
  field
    depthUpper :
      entryDepth i ≤ forcedTailSourceDepthCap N

record AdversarialTargetDef (N j : Nat) : Set where
  field
    depthLower :
      forcedTailSourceDepthCap N + advLogDepthRequired N ≤ entryDepth j

record TransitionTargetDef (N j : Nat) : Set where
  field
    depthLower :
      forcedTailSourceDepthCap N + transLogDepthRequired N ≤ entryDepth j

ForcedTailSource : Nat → Nat → Set
ForcedTailSource = ForcedTailSourceDef

AdversarialTarget : Nat → Nat → Set
AdversarialTarget = AdversarialTargetDef

TransitionTarget : Nat → Nat → Set
TransitionTarget = TransitionTargetDef
