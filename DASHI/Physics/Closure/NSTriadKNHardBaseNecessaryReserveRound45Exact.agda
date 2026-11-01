module DASHI.Physics.Closure.NSTriadKNHardBaseNecessaryReserveRound45Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Gyula Farkas.
-- Title: "Theorie der einfachen Ungleichungen".
-- Journal fuer die reine und angewandte Mathematik 124 (1902), 1--27.
-- DOI: no DOI assigned to the historical article.
--
-- DASHI CONTRIBUTION
--
-- Once HH-good is recognized as a positive Young-soft split, it should not be
-- included in the unavoidable-floor obstruction.  Define the hard base
--
--   H = 2 C_* + eta_Com + eta_kernel + 4/64.
--
-- The Round-45 total is exactly epsilon + H.  Since every PositiveThreshold
-- epsilon is strictly positive, any successful strict reserve implies H < 1.
-- Conversely H >= 1 refutes every possible HH-good split.  This analytically
-- eliminates the soft variable from the *necessary/no-go* side of the reserve
-- problem before invoking the full nine-dimensional dual machinery.
--
-- This theorem does not claim that H < 1 is sufficient without constructing a
-- rational positive split and the corresponding finite Gronwall coefficient;
-- it is the exact fail-closed hard-floor gate justified by the current types.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary.Negation using (¬_)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNLuoFiniteCriticalFourClassClosureExact as Critical
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHardSoftReserveRound45Exact as HardSoft

hardBaseEtaTotal :
  ∀ {environment} →
  HardSoft.HardSoftOwnerCore environment → ℚ
hardBaseEtaTotal core =
  Sharp.two * HardSoft.hhBadProfileCeiling core
  + Owner.eta (HardSoft.comEstimate core)
  + Owner.eta (HardSoft.kernelEstimate core)
  + Critical.oneSixtyFourth
  + Critical.oneSixtyFourth
  + Critical.oneSixtyFourth
  + Critical.oneSixtyFourth

hardSoftTotalIsSplitPlusHardBase :
  ∀ {environment}
    (core : HardSoft.HardSoftOwnerCore environment)
    (split : Threshold.PositiveThreshold) →
  HardSoft.hardSoftEtaTotal core split
  ≡ Threshold.threshold split + hardBaseEtaTotal core
hardSoftTotalIsSplitPlusHardBase core split =
  solve
    ( Threshold.threshold split
    ∷ Sharp.two * HardSoft.hhBadProfileCeiling core
    ∷ Owner.eta (HardSoft.comEstimate core)
    ∷ Owner.eta (HardSoft.kernelEstimate core)
    ∷ Critical.oneSixtyFourth
    ∷ [])

hardBaseBelowFullTotal :
  ∀ {environment}
    (core : HardSoft.HardSoftOwnerCore environment)
    (split : Threshold.PositiveThreshold) →
  hardBaseEtaTotal core ≤ HardSoft.hardSoftEtaTotal core split
hardBaseBelowFullTotal core split =
  let
    epsilonNN = Threshold.thresholdNonnegative split
    base = hardBaseEtaTotal core
    add : 0ℚ + base ≤ Threshold.threshold split + base
    add = ℚP.+-mono-≤ epsilonNN ℚP.≤-refl
  in
  subst
    (λ lower → lower ≤ HardSoft.hardSoftEtaTotal core split)
    (solve (base ∷ []))
    (subst
      (λ upper → 0ℚ + base ≤ upper)
      (sym (hardSoftTotalIsSplitPlusHardBase core split))
      add)

strictReserveImpliesHardBaseStrict :
  ∀ {environment}
    (core : HardSoft.HardSoftOwnerCore environment)
    (split : Threshold.PositiveThreshold) →
  HardSoft.HardSoftStrictReserveAtSplit core split →
  hardBaseEtaTotal core < 1ℚ
strictReserveImpliesHardBaseStrict core split reserve =
  ℚP.≤-<-trans
    (hardBaseBelowFullTotal core split)
    (HardSoft.reducedTotalStrict reserve)

hardBaseAtLeastOneRefutesEverySplit :
  ∀ {environment}
    (core : HardSoft.HardSoftOwnerCore environment) →
  1ℚ ≤ hardBaseEtaTotal core →
  ∀ split → ¬ HardSoft.HardSoftStrictReserveAtSplit core split
hardBaseAtLeastOneRefutesEverySplit core hardLower split reserve =
  let
    strictBase = strictReserveImpliesHardBaseStrict core split reserve
    impossible : 1ℚ < 1ℚ
    impossible = ℚP.≤-<-trans hardLower strictBase
  in
  ℚP.<-irrefl refl impossible

hhGoodSoftVariableEliminatedFromNecessaryGate : Bool
hhGoodSoftVariableEliminatedFromNecessaryGate = true

hhGoodSoftVariableEliminatedFromNecessaryGateIsTrue :
  hhGoodSoftVariableEliminatedFromNecessaryGate ≡ true
hhGoodSoftVariableEliminatedFromNecessaryGateIsTrue = refl
