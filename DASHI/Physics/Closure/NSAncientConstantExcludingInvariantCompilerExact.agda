module DASHI.Physics.Closure.NSAncientConstantExcludingInvariantCompilerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Authors: Gabriel Koch; Nikolai Nadirashvili; Gregory A. Seregin;
--          Vladimir Sverak.
-- Title: "Liouville theorems for the Navier-Stokes equations and applications".
-- DOI: 10.1007/s11511-009-0039-6.
--
-- SOURCE LOGIC
-- Proposition 6.1 produces a bounded ancient mild solution which is nonzero.
-- The authors immediately note that constants remain possible and that a
-- scale-invariant estimate excluding nonzero constants, combined with a
-- Liouville theorem, rules out the singularity.
--
-- This file is the exact constructive contradiction behind that observation.
-- It assumes neither the invariant nor the Liouville theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Nullary.Negation.Core using (¬_)

SpatiallyConstant : {X V : Set} → (X → V) → Set
SpatiallyConstant u = (x y : X) → u x ≡ u y

NonzeroAt : {X V : Set} → (V → Set) → (X → V) → Set
NonzeroAt IsNonzero u = (x : X) → IsNonzero (u x)

noBlowupFromConstantExcludingInvariant :
  {Blowup X V : Set} →
  (BoundedAncientMild : (X → V) → Set) →
  (Invariant : (X → V) → Set) →
  (IsNonzero : V → Set) →
  (extract : Blowup → X → V) →
  ((b : Blowup) → BoundedAncientMild (extract b)) →
  ((u : X → V) → BoundedAncientMild u → SpatiallyConstant u) →
  ((b : Blowup) → Invariant (extract b)) →
  ((u : X → V) → Invariant u → SpatiallyConstant u →
     ¬ ((x : X) → IsNonzero (u x))) →
  ((b : Blowup) → (x : X) → IsNonzero (extract b x)) →
  ¬ Blowup
noBlowupFromConstantExcludingInvariant
  BoundedAncientMild Invariant IsNonzero extract
  extractedBounded liouville inheritedInvariant invariantExcludesNonzeroConstants
  extractedNonzero blowup =
  invariantExcludesNonzeroConstants
    (extract blowup)
    (inheritedInvariant blowup)
    (liouville (extract blowup) (extractedBounded blowup))
    (extractedNonzero blowup)

-- In a source-faithful application, the final argument need only certify the
-- KNSŠ normalization at one point rather than every point.  A separate owner
-- can weaken NonzeroAt to a chosen basepoint once the physical carrier is
-- available.  This generic file keeps no hidden distinguished point.
