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
-- Proposition 6.1 produces a bounded ancient mild solution with a chosen
-- point normalized nonzero (their construction has |v(0,0)| = 1).
-- Constants remain possible.  KNSŠ explicitly note that any inherited
-- scale-invariant property excluding nonzero constants, combined with a
-- Liouville theorem, rules out the singularity.
--
-- This file is only that constructive contradiction.  It assumes neither the
-- physical invariant nor the Liouville theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Nullary.Negation.Core using (¬_)

SpatiallyConstant : {X V : Set} → (X → V) → Set
SpatiallyConstant u = (x y : X) → u x ≡ u y

noBlowupFromConstantExcludingInvariant :
  {Blowup X V : Set} →
  (basepoint : X) →
  (BoundedAncientMild : (X → V) → Set) →
  (Invariant : (X → V) → Set) →
  (IsNonzero : V → Set) →
  (extract : Blowup → X → V) →
  ((b : Blowup) → BoundedAncientMild (extract b)) →
  ((u : X → V) → BoundedAncientMild u → SpatiallyConstant u) →
  ((b : Blowup) → Invariant (extract b)) →
  ((u : X → V) → Invariant u → SpatiallyConstant u →
     ¬ IsNonzero (u basepoint)) →
  ((b : Blowup) → IsNonzero (extract b basepoint)) →
  ¬ Blowup
noBlowupFromConstantExcludingInvariant
  basepoint BoundedAncientMild Invariant IsNonzero extract
  extractedBounded liouville inheritedInvariant
  invariantExcludesNonzeroConstants extractedNonzero blowup =
  invariantExcludesNonzeroConstants
    (extract blowup)
    (inheritedInvariant blowup)
    (liouville (extract blowup) (extractedBounded blowup))
    (extractedNonzero blowup)
