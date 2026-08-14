module DASHI.Physics.Closure.NSTriadKNHHBadLiteralComponentFiniteTransientRound57Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- ROUND 57 CONTRIBUTION
--
-- Round 55 proved the finite-prefix/tail induction for affine recurrence
-- coefficients.  Round 57 has now exposed the stronger literal identity
--
--   C_(q+1) = I^lit_q + N^lit_q.
--
-- This file closes the finite-transient induction DIRECTLY on those physical
-- components.  After an arbitrary checked prefix, the only tail hypothesis is
--
--   N^lit_q <= C_* - I^lit_q.
--
-- There is no alpha, beta, sigma, uniform contraction constant, or auxiliary
-- minimal recurrence in the theorem statement.  The remaining hard theorem is
-- therefore exactly the PDE estimate on the literal inherited/generated/
-- leakage Duhamel quantities.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as Nat
import Data.Nat.Properties as NatP
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNHHBadRawVariableCapacityRound53Exact as Raw
import DASHI.Physics.Closure.NSTriadKNHHBadLiteralComponentCapacityRound57Exact as Components
import DASHI.Physics.Closure.NSTriadKNHHBadFiniteTransientTailBarrierRound55Exact as Prefix

record LiteralComponentFiniteTransientBarrier
    (physical : Raw.PhysicalGeneralVariableDefectDuhamel) : Set where
  field
    start : Nat
    ceiling : ℚ
    ceilingNonnegative : 0ℚ ≤ ceiling

    finitePrefixBelow : ∀ q → q Nat.≤ start →
      Raw.normalizedDefect physical q ≤ ceiling

    literalTailHeadroom : ∀ q → start Nat.≤ q →
      Components.literalGenerationFitsInheritedHeadroom physical ceiling q

open LiteralComponentFiniteTransientBarrier public

literalTailBelow :
  ∀ {physical}
    (barrier : LiteralComponentFiniteTransientBarrier physical) {q} →
  Prefix.TailAt (start barrier) q →
  Raw.normalizedDefect physical q ≤ ceiling barrier
literalTailBelow barrier Prefix.atStart =
  finitePrefixBelow barrier (start barrier) NatP.≤-refl
literalTailBelow {physical} barrier (Prefix.atStep {q} witness) =
  Components.literalComponentHeadroomPreservesCeiling
    physical (ceiling barrier) q
    (literalTailHeadroom barrier q (Prefix.tailAtOrder witness))

globalLiteralNormalizedDefectBelow :
  ∀ {physical}
    (barrier : LiteralComponentFiniteTransientBarrier physical) →
  ∀ q → Raw.normalizedDefect physical q ≤ ceiling barrier
globalLiteralNormalizedDefectBelow barrier q
  with Prefix.splitPrefixOrTail (start barrier) q
... | Prefix.prefix proof = finitePrefixBelow barrier q proof
... | Prefix.tail witness = literalTailBelow barrier witness

literalFiniteTransientNeedsNoAffineCoefficients : Bool
literalFiniteTransientNeedsNoAffineCoefficients = true

literalFiniteTransientNeedsNoAffineCoefficientsIsTrue :
  literalFiniteTransientNeedsNoAffineCoefficients ≡ true
literalFiniteTransientNeedsNoAffineCoefficientsIsTrue = refl
