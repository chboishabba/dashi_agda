module DASHI.Physics.YangMills.BalabanSU2FiniteBackgroundAssembly where

------------------------------------------------------------------------
-- Gauge-fixed finite-volume SU(2) background-field theorem assembly.
--
-- The analytic content remains explicit in the indexed contraction and Hessian
-- inputs. Once those are supplied, fixed-point existence, criticality,
-- uniqueness on the gauge slice, and minimization are derived here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanSU2NonlinearCriticalPointMap
open import DASHI.Physics.YangMills.BalabanSU2CriticalMapContraction

record SU2FiniteBackgroundInputs
    (Background Coarse Fluctuation Distance : Set) : Set₁ where
  field
    nonlinearMap : NonlinearCriticalPointMap Background Coarse Fluctuation
    contractionAt : Background → Coarse →
      FiniteCriticalContraction Fluctuation Distance

    stepMatchesCriticalMap : ∀ background coarse fluctuation →
      step (contractionAt background coarse) fluctuation
      ≡ criticalStep nonlinearMap background coarse fluctuation

    criticalImpliesFixed : ∀ background coarse fluctuation →
      criticalEquation nonlinearMap background coarse fluctuation →
      criticalStep nonlinearMap background coarse fluctuation ≡ fluctuation

    HessianCoercive : Background → Coarse → Fluctuation → Set
    hessianCoerciveAtCritical : ∀ background coarse fluctuation →
      criticalEquation nonlinearMap background coarse fluctuation →
      HessianCoercive background coarse fluctuation

    Minimizer : Background → Coarse → Fluctuation → Set
    criticalCoerciveImpliesMinimizer : ∀ background coarse fluctuation →
      criticalEquation nonlinearMap background coarse fluctuation →
      HessianCoercive background coarse fluctuation →
      Minimizer background coarse fluctuation

open SU2FiniteBackgroundInputs public

backgroundFluctuation :
  ∀ {Background Coarse Fluctuation Distance : Set} →
  SU2FiniteBackgroundInputs Background Coarse Fluctuation Distance →
  Background → Coarse → Fluctuation
backgroundFluctuation inputs background coarse =
  fixedPoint (contractionAt inputs background coarse)

backgroundFixed :
  ∀ {Background Coarse Fluctuation Distance : Set} →
  (inputs : SU2FiniteBackgroundInputs Background Coarse Fluctuation Distance) →
  ∀ background coarse →
  criticalStep (nonlinearMap inputs) background coarse
    (backgroundFluctuation inputs background coarse)
  ≡ backgroundFluctuation inputs background coarse
backgroundFixed inputs background coarse =
  trans
    (sym
      (stepMatchesCriticalMap inputs background coarse
        (backgroundFluctuation inputs background coarse)))
    (fixed (contractionAt inputs background coarse))

backgroundCritical :
  ∀ {Background Coarse Fluctuation Distance : Set} →
  (inputs : SU2FiniteBackgroundInputs Background Coarse Fluctuation Distance) →
  ∀ background coarse →
  criticalEquation (nonlinearMap inputs) background coarse
    (backgroundFluctuation inputs background coarse)
backgroundCritical inputs background coarse =
  fixedImpliesCritical (nonlinearMap inputs)
    background coarse
    (backgroundFluctuation inputs background coarse)
    (backgroundFixed inputs background coarse)

backgroundUniqueOnGaugeSlice :
  ∀ {Background Coarse Fluctuation Distance : Set} →
  (inputs : SU2FiniteBackgroundInputs Background Coarse Fluctuation Distance) →
  ∀ background coarse fluctuation →
  criticalEquation (nonlinearMap inputs) background coarse fluctuation →
  fluctuation ≡ backgroundFluctuation inputs background coarse
backgroundUniqueOnGaugeSlice inputs background coarse fluctuation critical =
  fixedPointUnique
    (contractionAt inputs background coarse)
    fluctuation
    (trans
      (stepMatchesCriticalMap inputs background coarse fluctuation)
      (criticalImpliesFixed inputs background coarse fluctuation critical))

backgroundMinimizes :
  ∀ {Background Coarse Fluctuation Distance : Set} →
  (inputs : SU2FiniteBackgroundInputs Background Coarse Fluctuation Distance) →
  ∀ background coarse →
  Minimizer inputs background coarse
    (backgroundFluctuation inputs background coarse)
backgroundMinimizes inputs background coarse =
  criticalCoerciveImpliesMinimizer inputs
    background coarse
    (backgroundFluctuation inputs background coarse)
    (backgroundCritical inputs background coarse)
    (hessianCoerciveAtCritical inputs
      background coarse
      (backgroundFluctuation inputs background coarse)
      (backgroundCritical inputs background coarse))

record GaugeOrbitLift
    (Background Coarse Fluctuation Gauge : Set)
    (Critical : Background → Coarse → Fluctuation → Set) : Set₁ where
  field
    gaugeAction : Gauge → Fluctuation → Fluctuation
    gaugeFix : Background → Coarse → Fluctuation → Fluctuation
    GaugeEquivalent : Fluctuation → Fluctuation → Set

    gaugeFixEquivalent : ∀ background coarse fluctuation →
      GaugeEquivalent fluctuation (gaugeFix background coarse fluctuation)
    gaugeFixPreservesCritical : ∀ background coarse fluctuation →
      Critical background coarse fluctuation →
      Critical background coarse (gaugeFix background coarse fluctuation)

open GaugeOrbitLift public

criticalOrbitContainsBackground :
  ∀ {Background Coarse Fluctuation Distance Gauge : Set} →
  (inputs : SU2FiniteBackgroundInputs Background Coarse Fluctuation Distance) →
  (orbit : GaugeOrbitLift Background Coarse Fluctuation Gauge
    (criticalEquation (nonlinearMap inputs))) →
  ∀ background coarse fluctuation →
  criticalEquation (nonlinearMap inputs) background coarse fluctuation →
  GaugeEquivalent orbit fluctuation
    (backgroundFluctuation inputs background coarse)
criticalOrbitContainsBackground inputs orbit background coarse fluctuation critical
  rewrite backgroundUniqueOnGaugeSlice inputs background coarse
    (gaugeFix orbit background coarse fluctuation)
    (gaugeFixPreservesCritical orbit background coarse fluctuation critical) =
  gaugeFixEquivalent orbit background coarse fluctuation

su2FiniteBackgroundAssemblyLevel : ProofLevel
su2FiniteBackgroundAssemblyLevel = machineChecked

su2FiniteBackgroundAnalyticInputsLevel : ProofLevel
su2FiniteBackgroundAnalyticInputsLevel = conditional
