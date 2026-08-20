module DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact where

------------------------------------------------------------------------
-- ROUND83: ONE MARKED ANALYTIC SHELL -> THREE CLAY-FACING CONSUMERS
--
-- PRIMARY SOURCES / CALIBRATION
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99(3) (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116(1) (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- David C. Brydges, John Dimock and Thomas R. Hurd,
-- "Estimates on Renormalization Group Transformations",
-- Canadian Journal of Mathematics 50 (1998), 756--793.
-- DOI: 10.4153/CJM-1998-041-5.
--
-- Stefan Hollands,
-- "The Operator Product Expansion for Perturbative Quantum Field Theory in
-- Curved Spacetime", Communications in Mathematical Physics 273 (2007), 1--36.
-- DOI: 10.1007/s00220-007-0230-6.
--
-- Bruno Nachtergaele, Anna Vershynina and Valentin A. Zagrebnov,
-- "Lieb-Robinson Bounds and Existence of the Thermodynamic Limit for a Class
-- of Irreversible Quantum Dynamics", Contemporary Mathematics 552 (2011),
-- 161--175. DOI: 10.1090/conm/552/10916.
--
-- DASHI CONTRIBUTION
--
-- The same differentiated, marked local activity appears in three places on
-- the shortest Clay route:
--
--   (A2) changing an earlier coupling changes the local polarization/beta;
--   (B2) differentiating the effective action gives the Langevin influence row;
--   (C1) differentiating with a local source gives composite/OPE increments.
--
-- Do not prove three unrelated exponential-decay theorems.  Put all three
-- projections below ONE positive analytic shell A_d and prove only
--
--        A_d <= C * rootedShell_d,
--        rootedShell_d <= (1/4) 2^{-d}.
--
-- The existing rooted-KP and weighted-Hessian compilers then imply, uniformly
-- in finite volume/cutoff,
--
--   sum_{d<n} beta_d      <= C/2,
--   sum_{d<n} composite_d <= C/2,
--   sum_{d<n} (3/2)^d h_d <= C.
--
-- Thus a single source-native marked analytic norm can control beta-history
-- stability, quasi-local stochastic propagation, and the geometric OPE tail.
-- The physical work is the one SAME-OBJECT analytic-shell estimate and the
-- identification of the three declared projections with the literal YM
-- quantities.  This file proves the downstream inequalities; it does not mark
-- that physical producer as completed.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayP2LargeFieldStepVExact as StepV
import DASHI.Physics.YangMills.BalabanRootedKPToHessianRowBudgetExact as Hess
import DASHI.Physics.YangMills.BalabanRootedKPToExponentialWeightedHessianExact as Weighted

record SharedMarkedAnalyticShellControl
    (Scale Volume Root : Set) : Set₁ where
  field
    kpShell : StepV.UniformRootedShellBound Scale Volume Root

    analyticShell : Scale → Volume → Root → Nat → ℚ
    analyticConstant : ℚ
    analyticConstantNonnegative : 0ℚ ≤ analyticConstant

    betaHistoryShell : Scale → Volume → Root → Nat → ℚ
    hessianInfluenceShell : Scale → Volume → Root → Nat → ℚ
    compositeInsertionShell : Scale → Volume → Root → Nat → ℚ

    analyticShellBelowRooted : ∀ scale volume root depth →
      analyticShell scale volume root depth
      ≤ analyticConstant * StepV.rootedShell kpShell scale volume root depth

    betaBelowAnalytic : ∀ scale volume root depth →
      betaHistoryShell scale volume root depth
      ≤ analyticShell scale volume root depth

    hessianBelowAnalytic : ∀ scale volume root depth →
      hessianInfluenceShell scale volume root depth
      ≤ analyticShell scale volume root depth

    compositeBelowAnalytic : ∀ scale volume root depth →
      compositeInsertionShell scale volume root depth
      ≤ analyticShell scale volume root depth

open SharedMarkedAnalyticShellControl public

responseControl :
  ∀ {Scale Volume Root}
    (dataSet : SharedMarkedAnalyticShellControl Scale Volume Root)
    (response : Scale → Volume → Root → Nat → ℚ) →
    (∀ scale volume root depth →
      response scale volume root depth
      ≤ analyticShell dataSet scale volume root depth) →
  Hess.RootedHessianShellControl Scale Volume Root
responseControl dataSet response responseBelow = record
  { Hess.RootedHessianShellControl.kpShell = kpShell dataSet
  ; Hess.RootedHessianShellControl.hessianRowShell = response
  ; Hess.RootedHessianShellControl.derivativeConstant = analyticConstant dataSet
  ; Hess.RootedHessianShellControl.derivativeConstantNonnegative =
      analyticConstantNonnegative dataSet
  ; Hess.RootedHessianShellControl.hessianShellBelowActivityShell =
      λ scale volume root depth →
        ℚP.≤-trans
          (responseBelow scale volume root depth)
          (analyticShellBelowRooted dataSet scale volume root depth)
  }

betaResponseControl :
  ∀ {Scale Volume Root} →
  SharedMarkedAnalyticShellControl Scale Volume Root →
  Hess.RootedHessianShellControl Scale Volume Root
betaResponseControl dataSet =
  responseControl dataSet (betaHistoryShell dataSet)
    (betaBelowAnalytic dataSet)

hessianResponseControl :
  ∀ {Scale Volume Root} →
  SharedMarkedAnalyticShellControl Scale Volume Root →
  Hess.RootedHessianShellControl Scale Volume Root
hessianResponseControl dataSet =
  responseControl dataSet (hessianInfluenceShell dataSet)
    (hessianBelowAnalytic dataSet)

compositeResponseControl :
  ∀ {Scale Volume Root} →
  SharedMarkedAnalyticShellControl Scale Volume Root →
  Hess.RootedHessianShellControl Scale Volume Root
compositeResponseControl dataSet =
  responseControl dataSet (compositeInsertionShell dataSet)
    (compositeBelowAnalytic dataSet)

betaHistoryPartial :
  ∀ {Scale Volume Root} →
  SharedMarkedAnalyticShellControl Scale Volume Root →
  Scale → Volume → Root → Nat → ℚ
betaHistoryPartial dataSet =
  Hess.hessianRowPartialSum (betaResponseControl dataSet)

compositeInsertionPartial :
  ∀ {Scale Volume Root} →
  SharedMarkedAnalyticShellControl Scale Volume Root →
  Scale → Volume → Root → Nat → ℚ
compositeInsertionPartial dataSet =
  Hess.hessianRowPartialSum (compositeResponseControl dataSet)

betaHistoryPartialBelowHalfAnalyticConstant :
  ∀ {Scale Volume Root}
    (dataSet : SharedMarkedAnalyticShellControl Scale Volume Root)
    scale volume root depth →
  betaHistoryPartial dataSet scale volume root depth
  ≤ StepV.half * analyticConstant dataSet
betaHistoryPartialBelowHalfAnalyticConstant dataSet =
  Hess.hessianRowPartialBelowHalfDerivativeConstant
    (betaResponseControl dataSet)

compositeInsertionPartialBelowHalfAnalyticConstant :
  ∀ {Scale Volume Root}
    (dataSet : SharedMarkedAnalyticShellControl Scale Volume Root)
    scale volume root depth →
  compositeInsertionPartial dataSet scale volume root depth
  ≤ StepV.half * analyticConstant dataSet
compositeInsertionPartialBelowHalfAnalyticConstant dataSet =
  Hess.hessianRowPartialBelowHalfDerivativeConstant
    (compositeResponseControl dataSet)

hessianWeightedControl :
  ∀ {Scale Volume Root} →
  SharedMarkedAnalyticShellControl Scale Volume Root →
  Weighted.ExponentialWeightedHessianShellControl Scale Volume Root
hessianWeightedControl dataSet = record
  { Weighted.ExponentialWeightedHessianShellControl.hessianControl =
      hessianResponseControl dataSet
  }

hessianWeightedInfluenceBelowAnalyticConstant :
  ∀ {Scale Volume Root}
    (dataSet : SharedMarkedAnalyticShellControl Scale Volume Root)
    scale volume root depth →
  Weighted.weightedHessianPartial
      (hessianWeightedControl dataSet) scale volume root depth
  ≤ analyticConstant dataSet
hessianWeightedInfluenceBelowAnalyticConstant dataSet =
  Weighted.weightedHessianRowUniformlyBelowDerivativeConstant
    (hessianWeightedControl dataSet)

sharedMarkedAnalyticThreeConsumerCompilerLevel : ProofLevel
sharedMarkedAnalyticThreeConsumerCompilerLevel = machineChecked

-- One new physical producer, not three unrelated decay receipts: instantiate
-- `analyticShell` by the literal twice/source-differentiated CMP99(3)/109/116
-- activity norm and prove its cutoff/volume-uniform rooted-shell comparison.
physicalSharedMarkedAnalyticShellLevel : ProofLevel
physicalSharedMarkedAnalyticShellLevel = conditional

-- Same-object identification remains essential: beta, Langevin Hessian and
-- composite insertion must really be projections of that one marked activity.
physicalSharedMarkedResponseIdentificationLevel : ProofLevel
physicalSharedMarkedResponseIdentificationLevel = conditional
