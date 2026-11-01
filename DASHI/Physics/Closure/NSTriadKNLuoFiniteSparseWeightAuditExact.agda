module DASHI.Physics.Closure.NSTriadKNLuoFiniteSparseWeightAuditExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Myong-Hwan Ri.
-- Title: "Global Regularity for the Navier--Stokes Equations with
-- Application to Global Solvability for the Euler Equations".
-- arXiv:2601.15685.
-- DOI: none assigned in the cited preprint version.
--
-- PURPOSE
-- Stress-test the sparse inverse-weight idea without importing its global
-- theorem claim.  If a shell penalty is at least one, then multiplying a
-- nonnegative critical shell term by that penalty can only increase the
-- finite critical sum.  Thus a sparse inverse-weight norm is not made
-- controllable by the L2 energy merely by inserting the weights; a separate
-- physical estimate is still required.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (subst)

record SparseShellSample : Set where
  constructor sparse-shell-sample
  field
    criticalTerm penalty : ℚ
    criticalTermNonnegative : 0ℚ ≤ criticalTerm
    oneBelowPenalty : 1ℚ ≤ penalty

open SparseShellSample public

ordinaryCriticalTerm : SparseShellSample → ℚ
ordinaryCriticalTerm sample = criticalTerm sample

sparseWeightedTerm : SparseShellSample → ℚ
sparseWeightedTerm sample = penalty sample * criticalTerm sample

sparseTermDominatesCritical :
  (sample : SparseShellSample) →
  ordinaryCriticalTerm sample ≤ sparseWeightedTerm sample
sparseTermDominatesCritical sample =
  let
    scaled :
      1ℚ * criticalTerm sample
      ≤ penalty sample * criticalTerm sample
    scaled =
      let
        instance
          termIsNonnegative =
            nonNegative (criticalTermNonnegative sample)
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (criticalTerm sample)
        (oneBelowPenalty sample)
  in
  subst
    (λ lower → lower ≤ sparseWeightedTerm sample)
    (ℚₚ.*-identityˡ (criticalTerm sample))
    scaled

sumBy : List SparseShellSample → (SparseShellSample → ℚ) → ℚ
sumBy [] value = 0ℚ
sumBy (sample ∷ samples) value =
  value sample + sumBy samples value

finiteSparseNormDominatesCritical :
  (samples : List SparseShellSample) →
  sumBy samples ordinaryCriticalTerm
  ≤ sumBy samples sparseWeightedTerm
finiteSparseNormDominatesCritical [] = ℚₚ.≤-refl
finiteSparseNormDominatesCritical (sample ∷ samples) =
  ℚₚ.+-mono-≤
    (sparseTermDominatesCritical sample)
    (finiteSparseNormDominatesCritical samples)
