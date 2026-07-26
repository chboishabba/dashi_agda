module DASHI.Physics.YangMills.BalabanPath4SU2BackgroundStabilityExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; _+_; _≤_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
  using (PhysicalSU2Tangent4)
open import DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact
  using (physicalTangentInner)
open import DASHI.Physics.YangMills.BalabanPath4SU2ConcretePropagatorExact
  using (configuredGaugeFixedMatrix)
import DASHI.Physics.YangMills.BalabanRelativeHessianCoercivity as Relative
import DASHI.Physics.YangMills.BalabanReferenceGreenPerturbation as Green

------------------------------------------------------------------------
-- Exact operator difference around the identity background.
------------------------------------------------------------------------

addTangent : PhysicalSU2Tangent4 → PhysicalSU2Tangent4 → PhysicalSU2Tangent4
addTangent left right component bond =
  left component bond + right component bond

record Path4SU2BackgroundHessianDifference (Background : Set) : Set₁ where
  field
    backgroundHessian : Background → PhysicalSU2Tangent4 → PhysicalSU2Tangent4
    hessianRemainder : Background → PhysicalSU2Tangent4 → PhysicalSU2Tangent4
    backgroundHessianDefinition : ∀ background tangent component bond →
      backgroundHessian background tangent component bond
      ≡ addTangent
          (configuredGaugeFixedMatrix tangent)
          (hessianRemainder background tangent)
          component bond

open Path4SU2BackgroundHessianDifference public

backgroundHessianDifferenceExact :
  ∀ {Background}
    (dataSet : Path4SU2BackgroundHessianDifference Background)
    background tangent component bond →
  backgroundHessian dataSet background tangent component bond
  ≡ addTangent
      (configuredGaugeFixedMatrix tangent)
      (hessianRemainder dataSet background tangent)
      component bond
backgroundHessianDifferenceExact dataSet =
  backgroundHessianDefinition dataSet

record Path4SU2BackgroundFormBound (Background : Set) : Set₁ where
  field
    differenceData : Path4SU2BackgroundHessianDifference Background
    perturbationSize : Background → ℚ
    perturbationMagnitude : Background → PhysicalSU2Tangent4 → ℚ
    backgroundHessianDifferenceBound : ∀ background tangent →
      perturbationMagnitude background tangent
      ≤ perturbationSize background
        Data.Rational._*_
        DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact.physicalUnweightedNormSq
          tangent

open Path4SU2BackgroundFormBound public

backgroundHessianDifferenceBound :
  ∀ {Background}
    (dataSet : Path4SU2BackgroundFormBound Background)
    background tangent →
  perturbationMagnitude dataSet background tangent
  ≤ perturbationSize dataSet background
    Data.Rational._*_
    DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact.physicalUnweightedNormSq
      tangent
backgroundHessianDifferenceBound dataSet =
  Path4SU2BackgroundFormBound.backgroundHessianDifferenceBound dataSet

------------------------------------------------------------------------
-- The small-background coercivity theorem is the already checked relative-form
-- argument, specialized here to the physical side-four tangent carrier.
------------------------------------------------------------------------

record Path4SU2SmallBackgroundCoercivity (Background : Set) : Set₁ where
  field
    relativeData :
      Relative.RelativeHessianCoercivityData
        Background PhysicalSU2Tangent4 ℚ

open Path4SU2SmallBackgroundCoercivity public

smallBackgroundPreservesCoercivity :
  ∀ {Background}
    (dataSet : Path4SU2SmallBackgroundCoercivity Background)
    background tangent →
  Relative.GaugeFixedTangent (relativeData dataSet) background tangent →
  Relative.LessEqual (relativeData dataSet)
    (Relative.scale (relativeData dataSet)
      (Relative.cH (relativeData dataSet))
      (Relative.normSq (relativeData dataSet) tangent))
    (Relative.inner (relativeData dataSet) tangent
      (Relative.fullHessian (relativeData dataSet) background tangent))
smallBackgroundPreservesCoercivity dataSet =
  Relative.relativePerturbationPreservesCoercivity (relativeData dataSet)

------------------------------------------------------------------------
-- Exact Neumann/resolvent factorization and composed Green bound.
------------------------------------------------------------------------

record Path4SU2BackgroundNeumannData (Background : Set) : Set₁ where
  field
    referenceGreen : Background → PhysicalSU2Tangent4 → PhysicalSU2Tangent4
    correctionInverse : Background → PhysicalSU2Tangent4 → PhysicalSU2Tangent4
    backgroundPropagator : Background → PhysicalSU2Tangent4 → PhysicalSU2Tangent4
    backgroundPropagatorDefinition : ∀ background source component bond →
      backgroundPropagator background source component bond
      ≡ referenceGreen background (correctionInverse background source)
          component bond

open Path4SU2BackgroundNeumannData public

backgroundPropagatorNeumannExpansion :
  ∀ {Background}
    (dataSet : Path4SU2BackgroundNeumannData Background)
    background source component bond →
  backgroundPropagator dataSet background source component bond
  ≡ referenceGreen dataSet background
      (correctionInverse dataSet background source) component bond
backgroundPropagatorNeumannExpansion dataSet =
  backgroundPropagatorDefinition dataSet

record Path4SU2BackgroundPropagatorBound (Background Bound : Set) : Set₁ where
  field
    perturbationData : Green.ReferenceGreenPerturbationData
      Background PhysicalSU2Tangent4 Bound

open Path4SU2BackgroundPropagatorBound public

backgroundPropagatorNormBound :
  ∀ {Background Bound}
    (dataSet : Path4SU2BackgroundPropagatorBound Background Bound)
    background source →
  Green.LessEqual (perturbationData dataSet)
    (Green.weightedNorm (perturbationData dataSet)
      (Green.muG (perturbationData dataSet))
      (Green.fullGreen (perturbationData dataSet) background source))
    (Green.multiply (perturbationData dataSet)
      (Green.multiply (perturbationData dataSet)
        (Green.referenceUpper (perturbationData dataSet))
        (Green.correctionUpper (perturbationData dataSet)))
      (Green.weightedNorm (perturbationData dataSet)
        (Green.muG (perturbationData dataSet)) source))
backgroundPropagatorNormBound dataSet =
  Green.composedBound
    (perturbationData dataSet)
    (Green.referenceGreen (perturbationData dataSet))
    (Green.referenceUpper (perturbationData dataSet))
    (Green.referenceGreenBound (perturbationData dataSet))

backgroundHessianDifferenceIdentityLevel : ProofLevel
backgroundHessianDifferenceIdentityLevel = machineChecked

backgroundHessianDifferenceBoundAssemblyLevel : ProofLevel
backgroundHessianDifferenceBoundAssemblyLevel = machineChecked

smallBackgroundCoercivityAssemblyLevel : ProofLevel
smallBackgroundCoercivityAssemblyLevel = machineChecked

backgroundPropagatorNeumannAssemblyLevel : ProofLevel
backgroundPropagatorNeumannAssemblyLevel = machineChecked

backgroundPerturbationProducerLevel : ProofLevel
backgroundPerturbationProducerLevel = conditional
