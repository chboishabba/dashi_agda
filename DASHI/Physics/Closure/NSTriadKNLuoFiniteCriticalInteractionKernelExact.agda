module DASHI.Physics.Closure.NSTriadKNLuoFiniteCriticalInteractionKernelExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Implement the finite summability part of the corrected shell-resolved
-- critical interaction functional.  The schematic kernel has three sectors:
--
-- * low shells with quarter-geometric decay;
-- * five comparable shells with unit weight;
-- * high shells with half-geometric decay.
--
-- Every finite prefix is bounded uniformly by
--
--   4/3 + 5 + 2 = 25/3.
--
-- This closes the discrete kernel bookkeeping.  It does not produce the
-- continuum classwise interaction estimates or critical terminal depletion.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _≤_)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNLuoFiniteHighHighLowDyadicGainExact as HH

five twentyFiveThirds : ℚ
five = Int.+ 5 / 1
twentyFiveThirds = Int.+ 25 / 3

lowKernelPrefix : Nat → ℚ
lowKernelPrefix cutoff = Geo.partialSum Geo.quarter cutoff

highKernelPrefix : Nat → ℚ
highKernelPrefix = HH.highHighLowGainPrefix

criticalKernelPrefix : Nat → Nat → ℚ
criticalKernelPrefix lowCutoff highCutoff =
  lowKernelPrefix lowCutoff + five + highKernelPrefix highCutoff

fiveReflexive : five ≤ five
fiveReflexive = toWitness {a? = five ≤? five} _

criticalKernelPrefixBound :
  (lowCutoff highCutoff : Nat) →
  criticalKernelPrefix lowCutoff highCutoff ≤ twentyFiveThirds
criticalKernelPrefixBound lowCutoff highCutoff =
  let
    lowAndComparable :
      lowKernelPrefix lowCutoff + five
      ≤ Geo.fourThirds + five
    lowAndComparable =
      ℚₚ.+-mono-≤
        (Geo.quarterPartialSumBound lowCutoff)
        fiveReflexive

    assembled :
      lowKernelPrefix lowCutoff + five + highKernelPrefix highCutoff
      ≤ Geo.fourThirds + five + HH.two
    assembled =
      ℚₚ.+-mono-≤
        lowAndComparable
        (HH.highHighLowGainPrefixBound highCutoff)

    targetMeaning :
      Geo.fourThirds + five + HH.two ≡ twentyFiveThirds
    targetMeaning = solve []
  in
  subst
    (λ upper → criticalKernelPrefix lowCutoff highCutoff ≤ upper)
    targetMeaning
    assembled
