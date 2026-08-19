module DASHI.Physics.Closure.NSTriadKNStrongSixThreeTwoDerivativePaymentRound89Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Piero D'Ancona.
-- Title: "A Short Proof of Commutator Estimates".
-- DOI: 10.1007/s00041-018-9612-8.
-- Correction DOI: 10.1007/s00041-019-09724-7.
--
-- Authors: Sean Douglas; Loukas Grafakos.
-- Title: "Norm Estimates for the Fractional Derivative of Multiple Factors".
-- DOI: 10.1016/j.jmaa.2024.128409.
--
-- ROUND89 / EXACT BRANCH-SELECTION CALIBRATION
--
-- The existing six-three centered-commutator calculation has two SQUARED gap
-- branches and one exact separation scale S_d:
--
--   g_s(d) = (1/64) (1/8)^d,
--   g_w(d) = (1/4)  (1/2)^d,
--   S_d    = 4 * 2^d.
--
-- Round88 observed that a viscous relative-growth coefficient costs two high
-- frequency powers.  This file proves the decisive exact identities
--
--   g_s(d) S_d^2 = g_w(d),
--   g_w(d) S_d^2 = S_d.
--
-- Hence the strong L6 branch pays TWO separation powers and leaves the
-- summable weak kernel, whereas charging the same two powers to the weak L3
-- branch produces a growing separation factor.  The theorem is exact rational
-- arithmetic on the repository's existing dyadic carrier.  It is not a new
-- continuum paraproduct theorem and does not assert that the literal physical
-- HH transfer has already been identified with g_s.
--
-- The source role is methodological/calibrating only: Bony/BCD separate
-- high-low paraproducts from the comparable-frequency remainder, D'Ancona
-- makes derivative gain visible after subtraction of principal product terms,
-- and Douglas--Grafakos distinguish the high-low Coifman--Meyer and high-high
-- shifted-square-function mechanisms.  The exact identities below are DASHI
-- consequences of already-proved repository formulas.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNLuoSixThreeCenteredCommutatorScaleExact as SixThree

strongPaysTwoSeparationPowers :
  (gap : Nat) →
  SixThree.strongBranchSquaredGap gap
    * (SixThree.separationScale gap * SixThree.separationScale gap)
  ≡ SixThree.weakBranchSquaredGap gap
strongPaysTwoSeparationPowers gap =
  let
    weak = SixThree.weakBranchSquaredGap gap
    sep = SixThree.separationScale gap
  in
  trans
    (cong
      (λ strong → strong * (sep * sep))
      (SixThree.strongGapCubeOfWeak gap))
    (trans
      (solve (weak ∷ sep ∷ []))
      (trans
        (cong (weak *_)
          (SixThree.weakGapSeparationCalibration gap))
        (solve (weak ∷ []))))

weakAfterTwoSeparationPowersGrowsToSeparation :
  (gap : Nat) →
  SixThree.weakBranchSquaredGap gap
    * (SixThree.separationScale gap * SixThree.separationScale gap)
  ≡ SixThree.separationScale gap
weakAfterTwoSeparationPowersGrowsToSeparation gap =
  let
    weak = SixThree.weakBranchSquaredGap gap
    sep = SixThree.separationScale gap
  in
  trans
    (solve (weak ∷ sep ∷ []))
    (trans
      (cong (_* sep)
        (SixThree.weakGapSeparationCalibration gap))
      (solve (sep ∷ [])))

strongPaysThreeSeparationPowersExactly :
  (gap : Nat) →
  SixThree.strongBranchSquaredGap gap
    * (SixThree.separationScale gap
      * SixThree.separationScale gap
      * SixThree.separationScale gap)
  ≡ 1ℚ
strongPaysThreeSeparationPowersExactly =
  SixThree.strongGapCubicSeparationCalibration

round89StrongSixThreePaysTwoViscousPowersExactly : Bool
round89StrongSixThreePaysTwoViscousPowersExactly = true

round89WeakSixThreePaysTwoViscousPowersUniformly : Bool
round89WeakSixThreePaysTwoViscousPowersUniformly = false

round89FarGapViscousVariationMustUseStrongBranch : Bool
round89FarGapViscousVariationMustUseStrongBranch = true

round89StrongSixThreePaysTwoViscousPowersExactlyIsTrue :
  round89StrongSixThreePaysTwoViscousPowersExactly ≡ true
round89StrongSixThreePaysTwoViscousPowersExactlyIsTrue = refl

round89WeakSixThreePaysTwoViscousPowersUniformlyIsFalse :
  round89WeakSixThreePaysTwoViscousPowersUniformly ≡ false
round89WeakSixThreePaysTwoViscousPowersUniformlyIsFalse = refl

round89FarGapViscousVariationMustUseStrongBranchIsTrue :
  round89FarGapViscousVariationMustUseStrongBranch ≡ true
round89FarGapViscousVariationMustUseStrongBranchIsTrue = refl
