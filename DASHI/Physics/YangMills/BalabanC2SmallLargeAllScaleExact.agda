module DASHI.Physics.YangMills.BalabanC2SmallLargeAllScaleExact where

open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPath4SU2BackgroundStabilityExact as Background
import DASHI.Physics.YangMills.BalabanRelativeHessianCoercivity as Relative
import DASHI.Physics.YangMills.BalabanExplicitStepVLargeField as StepV
import DASHI.Physics.YangMills.BalabanConcreteOneStepRG as OneStep
import DASHI.Physics.YangMills.BalabanOneStepPolymerEstimate as Polymer

------------------------------------------------------------------------
-- Concrete names for the small-field and large-field domains.
------------------------------------------------------------------------

record SmallFieldConfiguration (Field Bound : Set) : Set₁ where
  field
    field : Field
    curvatureSize : Bound
    admissibleRadius : Bound
    LessEqual : Bound → Bound → Set
    curvatureSmall : LessEqual curvatureSize admissibleRadius

open SmallFieldConfiguration public

record LargeFieldPolymer (Block PolymerCarrier Bound : Set) : Set₁ where
  field
    polymer : PolymerCarrier
    badBlock : Block
    actionDefect : Bound
    activityWeight : Bound

open LargeFieldPolymer public

smallFieldHessianUniformCoercivity :
  ∀ {BackgroundIndex}
    (dataSet : Background.Path4SU2SmallBackgroundCoercivity BackgroundIndex)
    background tangent →
  Relative.GaugeFixedTangent (Background.relativeData dataSet) background tangent →
  Relative.LessEqual (Background.relativeData dataSet)
    (Relative.scale (Background.relativeData dataSet)
      (Relative.cH (Background.relativeData dataSet))
      (Relative.normSq (Background.relativeData dataSet) tangent))
    (Relative.inner (Background.relativeData dataSet) tangent
      (Relative.fullHessian (Background.relativeData dataSet) background tangent))
smallFieldHessianUniformCoercivity =
  Background.smallBackgroundPreservesCoercivity

largeFieldActionPenalty :
  ∀ {Site PolymerCarrier Bound Cluster Observable}
    (dataSet : StepV.StepVLargeFieldData
      Site PolymerCarrier Bound Cluster Observable) →
  StepV.LargeFieldActionPenalty dataSet
largeFieldActionPenalty = StepV.largeFieldActionLowerBound

polymerActivitySuppression :
  ∀ {Site PolymerCarrier Bound Cluster Observable}
    (dataSet : StepV.StepVLargeFieldData
      Site PolymerCarrier Bound Cluster Observable) →
  StepV.LargeFieldActivitySuppression dataSet
polymerActivitySuppression = StepV.largeFieldPolymerSuppressed

------------------------------------------------------------------------
-- One-step coercivity transport and its exact all-scale induction.
------------------------------------------------------------------------

record CoercivityRGData (State : Set) : Set₁ where
  field
    renormalize : Nat → State → State
    CoerciveAt : Nat → State → Set
    oneStepRGCoercivityTransfer : ∀ scale state →
      CoerciveAt scale state →
      CoerciveAt (suc scale) (renormalize scale state)

open CoercivityRGData public

oneStepRGCoercivityTransfer :
  ∀ {State} (dataSet : CoercivityRGData State) scale state →
  CoerciveAt dataSet scale state →
  CoerciveAt dataSet (suc scale) (renormalize dataSet scale state)
oneStepRGCoercivityTransfer =
  CoercivityRGData.oneStepRGCoercivityTransfer

rgTrajectory :
  ∀ {State} → CoercivityRGData State → State → Nat → State
rgTrajectory dataSet initial zero = initial
rgTrajectory dataSet initial (suc scale) =
  renormalize dataSet scale (rgTrajectory dataSet initial scale)

allScaleCoercivity :
  ∀ {State} (dataSet : CoercivityRGData State) initial →
  CoerciveAt dataSet zero initial →
  ∀ scale → CoerciveAt dataSet scale (rgTrajectory dataSet initial scale)
allScaleCoercivity dataSet initial initialCoercive zero = initialCoercive
allScaleCoercivity dataSet initial initialCoercive (suc scale) =
  oneStepRGCoercivityTransfer dataSet scale
    (rgTrajectory dataSet initial scale)
    (allScaleCoercivity dataSet initial initialCoercive scale)

------------------------------------------------------------------------
-- Link to the existing quantitative one-step polymer contraction certificate.
------------------------------------------------------------------------

oneStepPolymerRGContraction :
  ∀ {F B Z J P R G}
    (dataSet : OneStep.ConcreteOneStepAnalyticData F B Z J P R G) →
  ∀ scale →
  Polymer.LessEqual (OneStep.order dataSet)
    (OneStep.polymerNorm dataSet (OneStep.E dataSet (suc scale)))
    (Polymer.add (OneStep.order dataSet)
      (OneStep.multiplyBound dataSet
        (OneStep.contractionFactor dataSet)
        (OneStep.polymerNorm dataSet (OneStep.E dataSet scale)))
      (OneStep.perturbativeError dataSet scale))
oneStepPolymerRGContraction = OneStep.oneStepPolymerContraction

smallFieldCoercivityAssemblyLevel : ProofLevel
smallFieldCoercivityAssemblyLevel = machineChecked

largeFieldStepVAssemblyLevel : ProofLevel
largeFieldStepVAssemblyLevel = machineChecked

oneStepRGCoercivityTransferLevel : ProofLevel
oneStepRGCoercivityTransferLevel = machineChecked

allScaleCoercivityInductionLevel : ProofLevel
allScaleCoercivityInductionLevel = machineChecked

smallFieldBackgroundEstimateProducerLevel : ProofLevel
smallFieldBackgroundEstimateProducerLevel = conditional

largeFieldActivityEstimateProducerLevel : ProofLevel
largeFieldActivityEstimateProducerLevel = conditional
