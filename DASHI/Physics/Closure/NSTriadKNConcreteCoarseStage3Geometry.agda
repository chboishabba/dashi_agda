module DASHI.Physics.Closure.NSTriadKNConcreteCoarseStage3Geometry where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalScaleTrichotomy as Scale
import DASHI.Physics.Closure.NSTriadKNPhysicalStage3Allocation as Allocation
import DASHI.Physics.Closure.NSTriadKNPhysicalScaleStage3Compatibility as Compatibility

------------------------------------------------------------------------
-- Concrete, exhaustive coarse candidate.
--
-- This is deliberately only the outer geometric classification:
--
--   forced-tail : low-high or high-low
--   transition  : comparable
--   adversarial : high-high-to-low
--   residual    : impossible at the coarse level
--
-- Phase, parity, orientation and polarization refinements remain properties
-- of the retained state and later coefficient estimates.  They are not used
-- to fake shell coverage.
------------------------------------------------------------------------

physicalIncidence :
  ∀ {carrier N}
    {policy : Allocation.RetainedStatePolicy carrier N} →
  Allocation.RetainedPhysicalTriad policy →
  Physical.PhysicalTriadIncidence
physicalIncidence τ = Allocation.incidence (Allocation.state τ)

isForcedTailRegime : Scale.ScaleRegime → Bool
isForcedTailRegime Scale.lowHigh = true
isForcedTailRegime Scale.highLow = true
isForcedTailRegime Scale.highHigh = false
isForcedTailRegime Scale.comparable = false

isTransitionRegime : Scale.ScaleRegime → Bool
isTransitionRegime Scale.lowHigh = false
isTransitionRegime Scale.highLow = false
isTransitionRegime Scale.highHigh = false
isTransitionRegime Scale.comparable = true

isAdversarialRegime : Scale.ScaleRegime → Bool
isAdversarialRegime Scale.lowHigh = false
isAdversarialRegime Scale.highLow = false
isAdversarialRegime Scale.highHigh = true
isAdversarialRegime Scale.comparable = false

CoarseForcedTail :
  ∀ {carrier N}
    {policy : Allocation.RetainedStatePolicy carrier N} →
  Scale.PhysicalShellPolicy →
  Allocation.RetainedPhysicalTriad policy → Set
CoarseForcedTail shellPolicy τ =
  Scale.classifyScale shellPolicy (physicalIncidence τ) ≡ Scale.lowHigh
  ⊎
  Scale.classifyScale shellPolicy (physicalIncidence τ) ≡ Scale.highLow

CoarseTransition :
  ∀ {carrier N}
    {policy : Allocation.RetainedStatePolicy carrier N} →
  Scale.PhysicalShellPolicy →
  Allocation.RetainedPhysicalTriad policy → Set
CoarseTransition shellPolicy τ =
  Scale.classifyScale shellPolicy (physicalIncidence τ) ≡ Scale.comparable

CoarseAdversarial :
  ∀ {carrier N}
    {policy : Allocation.RetainedStatePolicy carrier N} →
  Scale.PhysicalShellPolicy →
  Allocation.RetainedPhysicalTriad policy → Set
CoarseAdversarial shellPolicy τ =
  Scale.classifyScale shellPolicy (physicalIncidence τ) ≡ Scale.highHigh

CoarseResidual :
  ∀ {carrier N}
    {policy : Allocation.RetainedStatePolicy carrier N} →
  Scale.PhysicalShellPolicy →
  Allocation.RetainedPhysicalTriad policy → Set
CoarseResidual shellPolicy τ = ⊥

forcedTailDecision :
  ∀ {carrier N}
    {policy : Allocation.RetainedStatePolicy carrier N} →
  Scale.PhysicalShellPolicy →
  Allocation.RetainedPhysicalTriad policy → Bool
forcedTailDecision shellPolicy τ =
  isForcedTailRegime
    (Scale.classifyScale shellPolicy (physicalIncidence τ))

transitionDecision :
  ∀ {carrier N}
    {policy : Allocation.RetainedStatePolicy carrier N} →
  Scale.PhysicalShellPolicy →
  Allocation.RetainedPhysicalTriad policy → Bool
transitionDecision shellPolicy τ =
  isTransitionRegime
    (Scale.classifyScale shellPolicy (physicalIncidence τ))

adversarialDecision :
  ∀ {carrier N}
    {policy : Allocation.RetainedStatePolicy carrier N} →
  Scale.PhysicalShellPolicy →
  Allocation.RetainedPhysicalTriad policy → Bool
adversarialDecision shellPolicy τ =
  isAdversarialRegime
    (Scale.classifyScale shellPolicy (physicalIncidence τ))

forcedTailDecisionSound :
  ∀ {carrier N}
    {policy : Allocation.RetainedStatePolicy carrier N}
    (shellPolicy : Scale.PhysicalShellPolicy)
    (τ : Allocation.RetainedPhysicalTriad policy) →
  forcedTailDecision shellPolicy τ ≡ true →
  CoarseForcedTail shellPolicy τ
forcedTailDecisionSound shellPolicy τ proof
  with Scale.classifyScale shellPolicy (physicalIncidence τ)
... | Scale.lowHigh = inj₁ refl
... | Scale.highLow = inj₂ refl
... | Scale.highHigh with proof
...   | ()
... | Scale.comparable with proof
...   | ()

transitionDecisionSound :
  ∀ {carrier N}
    {policy : Allocation.RetainedStatePolicy carrier N}
    (shellPolicy : Scale.PhysicalShellPolicy)
    (τ : Allocation.RetainedPhysicalTriad policy) →
  transitionDecision shellPolicy τ ≡ true →
  CoarseTransition shellPolicy τ
transitionDecisionSound shellPolicy τ proof
  with Scale.classifyScale shellPolicy (physicalIncidence τ)
... | Scale.lowHigh with proof
...   | ()
... | Scale.highLow with proof
...   | ()
... | Scale.highHigh with proof
...   | ()
... | Scale.comparable = refl

adversarialDecisionSound :
  ∀ {carrier N}
    {policy : Allocation.RetainedStatePolicy carrier N}
    (shellPolicy : Scale.PhysicalShellPolicy)
    (τ : Allocation.RetainedPhysicalTriad policy) →
  adversarialDecision shellPolicy τ ≡ true →
  CoarseAdversarial shellPolicy τ
adversarialDecisionSound shellPolicy τ proof
  with Scale.classifyScale shellPolicy (physicalIncidence τ)
... | Scale.lowHigh with proof
...   | ()
... | Scale.highLow with proof
...   | ()
... | Scale.highHigh = refl
... | Scale.comparable with proof
...   | ()

noCoarseClassImpossible :
  (regime : Scale.ScaleRegime) →
  isForcedTailRegime regime ≡ false →
  isTransitionRegime regime ≡ false →
  isAdversarialRegime regime ≡ false →
  ⊥
noCoarseClassImpossible Scale.lowHigh ()
noCoarseClassImpossible Scale.highLow ()
noCoarseClassImpossible Scale.highHigh ft transition ()
noCoarseClassImpossible Scale.comparable ft ()

coarseResidualFallback :
  ∀ {carrier N}
    {policy : Allocation.RetainedStatePolicy carrier N}
    (shellPolicy : Scale.PhysicalShellPolicy)
    (τ : Allocation.RetainedPhysicalTriad policy) →
  forcedTailDecision shellPolicy τ ≡ false →
  transitionDecision shellPolicy τ ≡ false →
  adversarialDecision shellPolicy τ ≡ false →
  CoarseResidual shellPolicy τ
coarseResidualFallback shellPolicy τ ft tr adv =
  noCoarseClassImpossible
    (Scale.classifyScale shellPolicy (physicalIncidence τ))
    ft tr adv

concreteCoarseStage3Geometry :
  ∀ {carrier N}
    {policy : Allocation.RetainedStatePolicy carrier N} →
  Scale.PhysicalShellPolicy →
  Allocation.Stage3GeometricPredicates policy
concreteCoarseStage3Geometry shellPolicy =
  Allocation.stage3-geometric-predicates
    (CoarseForcedTail shellPolicy)
    (CoarseTransition shellPolicy)
    (CoarseAdversarial shellPolicy)
    (CoarseResidual shellPolicy)
    (forcedTailDecision shellPolicy)
    (transitionDecision shellPolicy)
    (adversarialDecision shellPolicy)
    (forcedTailDecisionSound shellPolicy)
    (transitionDecisionSound shellPolicy)
    (adversarialDecisionSound shellPolicy)
    (coarseResidualFallback shellPolicy)

------------------------------------------------------------------------
-- Exact compatibility of this candidate with the outer scale axis.
------------------------------------------------------------------------

data CoarseAllowedScale :
    Allocation.Stage3Class → Scale.ScaleRegime → Set where
  forcedTailLowHigh :
    CoarseAllowedScale Allocation.forcedTail Scale.lowHigh
  forcedTailHighLow :
    CoarseAllowedScale Allocation.forcedTail Scale.highLow
  transitionComparable :
    CoarseAllowedScale Allocation.transition Scale.comparable
  adversarialHighHigh :
    CoarseAllowedScale Allocation.adversarial Scale.highHigh

coarseAllocationScaleCompatible :
  ∀ {carrier N}
    {policy : Allocation.RetainedStatePolicy carrier N}
    (shellPolicy : Scale.PhysicalShellPolicy)
    (τ : Allocation.RetainedPhysicalTriad policy) →
  CoarseAllowedScale
    (Allocation.allocateStage3
      (concreteCoarseStage3Geometry shellPolicy) τ)
    (Scale.classifyScale shellPolicy (physicalIncidence τ))
coarseAllocationScaleCompatible shellPolicy τ
  with Scale.classifyScale shellPolicy (physicalIncidence τ)
... | Scale.lowHigh = forcedTailLowHigh
... | Scale.highLow = forcedTailHighLow
... | Scale.highHigh = adversarialHighHigh
... | Scale.comparable = transitionComparable

concreteCoarseStage3RefinesScale :
  ∀ {carrier N}
    {policy : Allocation.RetainedStatePolicy carrier N}
    (shellPolicy : Scale.PhysicalShellPolicy) →
  Compatibility.Stage3AllocationRefinesScale
    shellPolicy
    (concreteCoarseStage3Geometry shellPolicy)
concreteCoarseStage3RefinesScale shellPolicy =
  Compatibility.stage3-allocation-refines-scale
    CoarseAllowedScale
    (coarseAllocationScaleCompatible shellPolicy)

concreteCoarsePhysicalPredicatesImplemented : Bool
concreteCoarsePhysicalPredicatesImplemented = true

concreteCoarsePhysicalPredicatesImplementedIsTrue :
  concreteCoarsePhysicalPredicatesImplemented ≡ true
concreteCoarsePhysicalPredicatesImplementedIsTrue = refl

coarseScaleCompatibilityImplemented : Bool
coarseScaleCompatibilityImplemented = true

coarseScaleCompatibilityImplementedIsTrue :
  coarseScaleCompatibilityImplemented ≡ true
coarseScaleCompatibilityImplementedIsTrue = refl
