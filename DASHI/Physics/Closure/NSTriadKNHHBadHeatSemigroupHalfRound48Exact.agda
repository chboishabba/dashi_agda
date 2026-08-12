module DASHI.Physics.Closure.NSTriadKNHHBadHeatSemigroupHalfRound48Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- The repository already contains an exact rational model in which one
-- resolved parabolic heat-time unit contributes damping 1/2.  This module asks
-- the physically meaningful same-object question for HH-bad inheritance:
--
--   is the inherited directional-defect component at q+1 literally one
--   parabolic heat unit applied to an alpha-contracted q-shell component?
--
-- If yes, the required recurrence half is automatic.  If not, the heat model
-- cannot be cited as the source of the half.  This is a candidate mechanism,
-- not a promotion of the physical identity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicHeatDampingExact as Heat

oneHeatUnitIsHalf : Heat.heatDamping (Agda.Builtin.Nat.suc Agda.Builtin.Nat.zero)
  ≡ Sharp.half
oneHeatUnitIsHalf = refl

record PhysicalOneHeatUnitInheritance : Set where
  field
    previousDefect inheritedDefect alpha : ℚ
    inheritedFromOneHeatUnit :
      inheritedDefect
      ≤ alpha * previousDefect
        * Heat.heatDamping (Agda.Builtin.Nat.suc Agda.Builtin.Nat.zero)

open PhysicalOneHeatUnitInheritance public

oneHeatUnitInheritanceGivesRequiredHalf :
  (physical : PhysicalOneHeatUnitInheritance) →
  inheritedDefect physical
  ≤ alpha physical * Sharp.half * previousDefect physical
oneHeatUnitInheritanceGivesRequiredHalf physical =
  let
    targetMeaning :
      alpha physical * previousDefect physical
        * Heat.heatDamping (Agda.Builtin.Nat.suc Agda.Builtin.Nat.zero)
      ≡ alpha physical * Sharp.half * previousDefect physical
    targetMeaning = solve
      (alpha physical ∷ previousDefect physical ∷ [])
  in
  subst
    (λ upper → inheritedDefect physical ≤ upper)
    targetMeaning
    (inheritedFromOneHeatUnit physical)

hhBadHeatSemigroupHalfCandidateClosed : Bool
hhBadHeatSemigroupHalfCandidateClosed = true

physicalHHBadInheritanceIdentifiedWithOneHeatUnit : Bool
physicalHHBadInheritanceIdentifiedWithOneHeatUnit = false

hhBadHeatSemigroupHalfCandidateClosedIsTrue :
  hhBadHeatSemigroupHalfCandidateClosed ≡ true
hhBadHeatSemigroupHalfCandidateClosedIsTrue = refl

physicalHHBadInheritanceIdentifiedWithOneHeatUnitIsFalse :
  physicalHHBadInheritanceIdentifiedWithOneHeatUnit ≡ false
physicalHHBadInheritanceIdentifiedWithOneHeatUnitIsFalse = refl
