module DASHI.Physics.YangMills.BalabanP11LightweightCanonicalPaymentExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Roman Kotecký and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- PURPOSE
-- Feed the canonical constant produced by the lightweight P06 receipt directly
-- into the finite Step-V/P11 summation lane.  P11 may not request a second,
-- unrelated animal-counting witness.  Once the physical activity ratio and the
-- direct successor-absorption inequality are supplied, the uniform finite
-- weighted-shell bound is a theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.YangMills.BalabanP06PhysicalModelLeafLightweightExact as P06
import DASHI.Physics.YangMills.BalabanStepVFiniteGeometricBackendExact as StepV
import DASHI.Physics.YangMills.BalabanStepVFiniteGeometricInductionExact as Geometric
import DASHI.Physics.YangMills.BalabanStepVPolynomialDirectRatioExact as DirectRatio
open import DASHI.Physics.YangMills.CompactLieProofLevel

canonicalAnimalConstantFromLightweightReceipt :
  ∀ {leaf} →
  P06.P06LightweightPhysicalReceipt leaf → Nat
canonicalAnimalConstantFromLightweightReceipt receipt =
  P06.animalConstant receipt

record P11LightweightCanonicalPayment
    (leaf : P06.P06LightweightPhysicalModelLeaf) : Set₁ where
  field
    p06Receipt : P06.P06LightweightPhysicalReceipt leaf

    Scalar : Set
    kernel : StepV.OrderedSemiringKernel Scalar
    laws : Geometric.GeometricSemiringLaws kernel

    fromNat : Nat → Scalar
    activityDecayRatio : Scalar

    combinedAnimalActivityRatio : Scalar
    combinedRatioDefinition :
      combinedAnimalActivityRatio
      ≡ StepV.multiply kernel
          (fromNat
            (canonicalAnimalConstantFromLightweightReceipt p06Receipt))
          activityDecayRatio

    polynomialDegree : Nat

    directRatioInputs :
      DirectRatio.PolynomialDirectRatioInputs
        kernel laws combinedAnimalActivityRatio polynomialDegree

    finitePrefixUsesActualStartupScales : Set
    finitePrefixUsesActualStartupScalesEvidence :
      finitePrefixUsesActualStartupScales

    activityDecayComesFromP10AndP33 : Set
    activityDecayComesFromP10AndP33Evidence :
      activityDecayComesFromP10AndP33

    shellDecompositionMatchesPhysicalKPNeighbourhood : Set
    shellDecompositionMatchesPhysicalKPNeighbourhoodEvidence :
      shellDecompositionMatchesPhysicalKPNeighbourhood

    theoremBoundary : String

open P11LightweightCanonicalPayment public

p11LightweightWeightedShellBound :
  ∀ {leaf} →
  (inputs : P11LightweightCanonicalPayment leaf) →
  StepV.PolynomiallyWeightedGeometricBound
    (kernel inputs)
    (combinedAnimalActivityRatio inputs)
    (polynomialDegree inputs)
p11LightweightWeightedShellBound inputs =
  DirectRatio.polynomialWeightedBoundFromDirectRatio
    (directRatioInputs inputs)

record P11LightweightCanonicalReceipt
    {leaf : P06.P06LightweightPhysicalModelLeaf}
    (inputs : P11LightweightCanonicalPayment leaf) : Set₁ where
  field
    animalConstant : Nat
    animalConstantIsP06Canonical :
      animalConstant
      ≡ P06.canonicalSkeletonDecorationAnimalConstant leaf

    weightedShellBound :
      StepV.PolynomiallyWeightedGeometricBound
        (kernel inputs)
        (combinedAnimalActivityRatio inputs)
        (polynomialDegree inputs)

    theoremBoundary : String

open P11LightweightCanonicalReceipt public

p11LightweightCanonicalReceipt :
  ∀ {leaf} →
  (inputs : P11LightweightCanonicalPayment leaf) →
  P11LightweightCanonicalReceipt inputs
p11LightweightCanonicalReceipt {leaf} inputs = record
  { animalConstant =
      canonicalAnimalConstantFromLightweightReceipt
        (p06Receipt inputs)
  ; animalConstantIsP06Canonical =
      P06.animalConstantIsCanonical (p06Receipt inputs)
  ; weightedShellBound = p11LightweightWeightedShellBound inputs
  ; theoremBoundary =
      "P11 lightweight receipt: the only animal constant is the canonical P06 skeleton-decoration-fibre constant; direct-ratio absorption supplies the finite weighted-shell bound without a logarithm backend."
  }

p11LightweightCanonicalConstantLevel : ProofLevel
p11LightweightCanonicalConstantLevel = machineChecked

p11LightweightWeightedShellReducerLevel : ProofLevel
p11LightweightWeightedShellReducerLevel = machineChecked

p11PhysicalStartupActivityAndNeighbourhoodInputsLevel : ProofLevel
p11PhysicalStartupActivityAndNeighbourhoodInputsLevel = conditional
