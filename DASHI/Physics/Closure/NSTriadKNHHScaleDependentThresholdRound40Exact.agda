module DASHI.Physics.Closure.NSTriadKNHHScaleDependentThresholdRound40Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Do not assume before the physical estimates are known that the HH threshold
-- must be scale independent.  Let each shell q have physical constants A_q,
-- B_q and a positive scale r_q (delta_q = r_q^2).  If
--
--   A_q r_q^3 = 2 B_q,
--
-- Round 40's exact symbolic optimizer proves r_q minimizes
--
--   A_q r + B_q r^{-2}
--
-- at that shell.  This module lifts the theorem pointwise and to arbitrary
-- finite shell lists.  It also proves that if all certified r_q are literally
-- the same positive scale, that common scale minimizes the whole finite HH tax.
-- Thus scale-independent delta is recovered as a theorem when the physical
-- constants force it, rather than imposed as an architectural assumption.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHAnalyticThresholdOptimizerRound40Exact as Opt

record ShellHHThresholdProfile : Set₁ where
  field
    A B : Nat → ℚ
    balanced : (shell : Nat) → Opt.BalancedHHThreshold (A shell) (B shell)

open ShellHHThresholdProfile public

selectedScaleAt : ShellHHThresholdProfile → Nat → Threshold.PositiveThreshold
selectedScaleAt profile shell = Opt.selectedScale (balanced profile shell)

shellTax :
  ShellHHThresholdProfile → Nat → Threshold.PositiveThreshold → ℚ
shellTax profile shell scale =
  Opt.combinedHHTax (A profile shell) (B profile shell) scale

shellSelectedIsGlobalMinimum :
  (profile : ShellHHThresholdProfile) →
  (shell : Nat) →
  (candidate : Threshold.PositiveThreshold) →
  shellTax profile shell (selectedScaleAt profile shell)
  ≤ shellTax profile shell candidate
shellSelectedIsGlobalMinimum profile shell candidate =
  Opt.globalBalancedThresholdMinimum (balanced profile shell) candidate

finiteShellTax :
  ShellHHThresholdProfile →
  List Nat →
  (Nat → Threshold.PositiveThreshold) → ℚ
finiteShellTax profile [] scales = 0ℚ
finiteShellTax profile (shell ∷ rest) scales =
  shellTax profile shell (scales shell)
  + finiteShellTax profile rest scales

selectedScales :
  ShellHHThresholdProfile → Nat → Threshold.PositiveThreshold
selectedScales = selectedScaleAt

finiteSelectedScalesMinimize :
  (profile : ShellHHThresholdProfile) →
  (shells : List Nat) →
  (candidate : Nat → Threshold.PositiveThreshold) →
  finiteShellTax profile shells (selectedScales profile)
  ≤ finiteShellTax profile shells candidate
finiteSelectedScalesMinimize profile [] candidate = ℚP.≤-refl
finiteSelectedScalesMinimize profile (shell ∷ rest) candidate =
  ℚP.+-mono-≤
    (shellSelectedIsGlobalMinimum profile shell (candidate shell))
    (finiteSelectedScalesMinimize profile rest candidate)

record ScaleIndependentBalancedThreshold
    (profile : ShellHHThresholdProfile) : Set where
  field
    commonScale : Threshold.PositiveThreshold
    selectedScaleIsCommon :
      (shell : Nat) → selectedScaleAt profile shell ≡ commonScale

open ScaleIndependentBalancedThreshold public

constantScales : Threshold.PositiveThreshold → Nat → Threshold.PositiveThreshold
constantScales scale shell = scale

commonScaleMinimizesEveryShell :
  ∀ {profile} →
  (certificate : ScaleIndependentBalancedThreshold profile) →
  (shell : Nat) →
  (candidate : Threshold.PositiveThreshold) →
  shellTax profile shell (commonScale certificate)
  ≤ shellTax profile shell candidate
commonScaleMinimizesEveryShell {profile} certificate shell candidate =
  subst
    (λ chosen →
      shellTax profile shell chosen ≤ shellTax profile shell candidate)
    (selectedScaleIsCommon certificate shell)
    (shellSelectedIsGlobalMinimum profile shell candidate)

commonScaleMinimizesFiniteShellTax :
  ∀ {profile} →
  (certificate : ScaleIndependentBalancedThreshold profile) →
  (shells : List Nat) →
  (candidate : Threshold.PositiveThreshold) →
  finiteShellTax profile shells (constantScales (commonScale certificate))
  ≤ finiteShellTax profile shells (constantScales candidate)
commonScaleMinimizesFiniteShellTax certificate [] candidate = ℚP.≤-refl
commonScaleMinimizesFiniteShellTax {profile} certificate
    (shell ∷ rest) candidate =
  ℚP.+-mono-≤
    (commonScaleMinimizesEveryShell certificate shell candidate)
    (commonScaleMinimizesFiniteShellTax certificate rest candidate)

scaleDependentThresholdDiagnosticClosed : Bool
scaleDependentThresholdDiagnosticClosed = true

physicalShellHHConstantsConstructed : Bool
physicalShellHHConstantsConstructed = false

scaleDependentThresholdDiagnosticClosedIsTrue :
  scaleDependentThresholdDiagnosticClosed ≡ true
scaleDependentThresholdDiagnosticClosedIsTrue = refl
