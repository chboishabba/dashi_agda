module DASHI.Physics.Closure.NSTriadKNPhysicalScaleStage3Compatibility where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)

import DASHI.Physics.Closure.NSTriadKNPhysicalScaleTrichotomy as Scale
import DASHI.Physics.Closure.NSTriadKNPhysicalStage3Allocation as Allocation

------------------------------------------------------------------------
-- Scale classification and Stage-3 allocation are deliberately different
-- axes.  Every retained state receives both classifications.  A separate
-- compatibility theorem states which coarse shell regimes are allowed for
-- each geometric/phase class.
------------------------------------------------------------------------

record ScaleAndStage3Classification
    {carrier : Allocation.TriadStateCarrier}
    {N : Nat}
    {retainedPolicy : Allocation.RetainedStatePolicy carrier N}
    (shellPolicy : Scale.PhysicalShellPolicy)
    (geometry : Allocation.Stage3GeometricPredicates retainedPolicy)
    (τ : Allocation.RetainedPhysicalTriad retainedPolicy) : Set where
  constructor scale-and-stage3
  field
    scaleRegime : Scale.ScaleRegime
    scaleEvidence :
      Scale.ScaleCondition shellPolicy
        (Allocation.incidence (Allocation.state τ))
        scaleRegime
    stage3Class : Allocation.Stage3Class
    stage3Evidence :
      Allocation.AllocationEvidence geometry τ stage3Class

open ScaleAndStage3Classification public

classifyOnBothAxes :
  ∀ {carrier N}
    {retainedPolicy : Allocation.RetainedStatePolicy carrier N} →
  (shellPolicy : Scale.PhysicalShellPolicy) →
  (geometry : Allocation.Stage3GeometricPredicates retainedPolicy) →
  (τ : Allocation.RetainedPhysicalTriad retainedPolicy) →
  ScaleAndStage3Classification shellPolicy geometry τ
classifyOnBothAxes shellPolicy geometry τ =
  scale-and-stage3
    (Scale.classifyScale shellPolicy
      (Allocation.incidence (Allocation.state τ)))
    (Scale.scaleClassificationSound shellPolicy
      (Allocation.incidence (Allocation.state τ)))
    (Allocation.allocateStage3 geometry τ)
    (Allocation.allocationSound geometry τ)

record Stage3AllocationRefinesScale
    {carrier : Allocation.TriadStateCarrier}
    {N : Nat}
    {retainedPolicy : Allocation.RetainedStatePolicy carrier N}
    (shellPolicy : Scale.PhysicalShellPolicy)
    (geometry : Allocation.Stage3GeometricPredicates retainedPolicy) : Set₁ where
  constructor stage3-allocation-refines-scale
  field
    AllowedScale :
      Allocation.Stage3Class → Scale.ScaleRegime → Set

    allocationScaleCompatible :
      (τ : Allocation.RetainedPhysicalTriad retainedPolicy) →
      AllowedScale
        (Allocation.allocateStage3 geometry τ)
        (Scale.classifyScale shellPolicy
          (Allocation.incidence (Allocation.state τ)))

open Stage3AllocationRefinesScale public

twoAxisClassificationImplemented : Bool
twoAxisClassificationImplemented = true

twoAxisClassificationImplementedIsTrue :
  twoAxisClassificationImplemented ≡ true
twoAxisClassificationImplementedIsTrue = refl

stage3ScaleRefinementTheoremInhabited : Bool
stage3ScaleRefinementTheoremInhabited = false

stage3ScaleRefinementTheoremInhabitedIsFalse :
  stage3ScaleRefinementTheoremInhabited ≡ false
stage3ScaleRefinementTheoremInhabitedIsFalse = refl
