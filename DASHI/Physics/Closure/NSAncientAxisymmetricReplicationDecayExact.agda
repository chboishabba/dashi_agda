module DASHI.Physics.Closure.NSAncientAxisymmetricReplicationDecayExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Authors: Zhen Lei; Qi S. Zhang; Na Zhao.
-- Title: "Improved Liouville theorems for axially symmetric Navier-Stokes
--         equations".
-- DOI: 10.1360/N012016-00149.
-- arXiv: 1701.00868.
--
-- SOURCE MECHANISM
-- In Lemma 5.1, axial symmetry lets one place many disjoint unit balls on a
-- large circle, all carrying the same local integral of |Gamma|^p.  Since the
-- sum of those copies is bounded by the global L^p mass, the local mass is
-- bounded by the reciprocal number of copies times the global mass.  This is
-- the algebraic core of equation (5.11).
--
-- The geometric facts "disjoint" and "equal by symmetry" are intentionally
-- outside this file.  Given their resulting mass inequality, the reciprocal
-- decay below is exact ordered-rational arithmetic.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

replicationForcesReciprocalLocalMassBound :
  (copies inverseCopies localMass totalMass : ℚ) →
  inverseCopies * copies ≡ 1ℚ →
  0ℚ ≤ inverseCopies →
  copies * localMass ≤ totalMass →
  localMass ≤ inverseCopies * totalMass
replicationForcesReciprocalLocalMassBound
  copies inverseCopies localMass totalMass reciprocal inverseNonnegative replicatedBound =
  let
    instance inverseNN : NonNegative inverseCopies
        inverseNN = nonNegative inverseNonnegative

    multiplied :
      inverseCopies * (copies * localMass)
      ≤ inverseCopies * totalMass
    multiplied = ℚP.*-monoˡ-≤-nonNeg inverseCopies replicatedBound

    regroup :
      inverseCopies * (copies * localMass)
      ≡ (inverseCopies * copies) * localMass
    regroup = solve (inverseCopies ∷ copies ∷ localMass ∷ [])

    replaceCopies :
      (inverseCopies * copies) * localMass
      ≡ 1ℚ * localMass
    replaceCopies = cong (_* localMass) reciprocal

    leftMeaning :
      inverseCopies * (copies * localMass) ≡ localMass
    leftMeaning =
      trans regroup
        (trans replaceCopies (ℚP.*-identityˡ localMass))
  in
  subst
    (_≤ inverseCopies * totalMass)
    leftMeaning
    multiplied

-- For the Lei-Zhang-Zhao application:
--   copies       ~ floor(r),
--   inverseCopies ~ 1/floor(r),
--   localMass     = integral over one unit ball of |Gamma|^p,
--   totalMass     = global integral of |Gamma|^p.
-- The remaining limit inverseCopies -> 0 is an Archimedean/real-analysis
-- step, not hidden here.
