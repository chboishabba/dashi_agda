module DASHI.Physics.YangMills.BalabanP11PhysicalPrefixTailEntropyExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Roman Kotecký and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.YangMills.BalabanPolymerDiameterEntropy as Entropy
import DASHI.Physics.YangMills.BalabanP06CanonicalAnimalConstantExact as P06
import DASHI.Physics.YangMills.BalabanP11PrefixTailMinimumExact as P11
import DASHI.Physics.YangMills.BalabanLargeFieldSuppression as LargeField
open import DASHI.Physics.YangMills.CompactLieProofLevel

record P11AnimalEntropyAccounting
    (modelLeaf : Entropy.P06ModelLeafDischargePackage) : Set₁ where
  field
    boundaryOverhead : Nat
    decorationOverhead : Nat
    canonicalAnimalConstantIsUsed : Set
    canonicalAnimalConstantIsUsedEvidence :
      canonicalAnimalConstantIsUsed
    logarithmicAnimalEntropy : Set
    logarithmicAnimalEntropyEvidence : logarithmicAnimalEntropy
    entropyThresholdEqualsAnimalBoundaryDecorationCost : Set
    entropyThresholdEqualsAnimalBoundaryDecorationCostEvidence :
      entropyThresholdEqualsAnimalBoundaryDecorationCost

open P11AnimalEntropyAccounting public

record P11PhysicalPrefixTailInputs : Set₁ where
  field
    modelLeaf : Entropy.P06ModelLeafDischargePackage
    entropyAccounting : P11AnimalEntropyAccounting modelLeaf
    analyticPrefixTail : P11.P11PrefixTailAnalyticInputs
    finitePrefixBoundsAreExact : Set
    finitePrefixBoundsAreExactEvidence : finitePrefixBoundsAreExact
    asymptoticTailBoundUsesRunningCoupling : Set
    asymptoticTailBoundUsesRunningCouplingEvidence :
      asymptoticTailBoundUsesRunningCoupling
    noGeometricGainInferredFromPolylogGrowth : Set
    noGeometricGainInferredFromPolylogGrowthEvidence :
      noGeometricGainInferredFromPolylogGrowth
    entropyPaymentUsesCanonicalAnimalConstant : Set
    entropyPaymentUsesCanonicalAnimalConstantEvidence :
      entropyPaymentUsesCanonicalAnimalConstant

open P11PhysicalPrefixTailInputs public

canonicalAnimalConstantForP11 :
  P11PhysicalPrefixTailInputs → Nat
canonicalAnimalConstantForP11 inputs =
  P06.canonicalAnimalConstant (modelLeaf inputs)

p11AnalyticInputsFromPhysical :
  P11PhysicalPrefixTailInputs →
  P11.P11PrefixTailAnalyticInputs
p11AnalyticInputsFromPhysical = analyticPrefixTail

p11AbsorptionFromPhysicalPrefixTail :
  P11PhysicalPrefixTailInputs →
  LargeField.ImportedAbsorptionCondition
p11AbsorptionFromPhysicalPrefixTail inputs =
  P11.p11AbsorptionConditionFromAnalyticPrefixTail
    (analyticPrefixTail inputs)

record P11PhysicalReceipt
    (inputs : P11PhysicalPrefixTailInputs) : Set₁ where
  field
    animalConstant : Nat
    animalConstantIsCanonical :
      animalConstant ≡ canonicalAnimalConstantForP11 inputs
    absorption : LargeField.ImportedAbsorptionCondition
    theoremBoundary : String

open P11PhysicalReceipt public

p11PhysicalReceipt :
  (inputs : P11PhysicalPrefixTailInputs) →
  P11PhysicalReceipt inputs
p11PhysicalReceipt inputs = record
  { animalConstant = canonicalAnimalConstantForP11 inputs
  ; animalConstantIsCanonical = refl
  ; absorption = p11AbsorptionFromPhysicalPrefixTail inputs
  ; theoremBoundary =
      "P11 physical receipt: exact startup bounds, asymptotic p0 lower bound and one scalar entropy payment using the canonical P06 animal constant produce the non-postulated absorption witness."
  }

p11PhysicalAssemblyLevel : ProofLevel
p11PhysicalAssemblyLevel = machineChecked
p11FinitePrefixEstimateLevel : ProofLevel
p11FinitePrefixEstimateLevel = conditional
p11AsymptoticTailEstimateLevel : ProofLevel
p11AsymptoticTailEstimateLevel = conditional
p11CanonicalEntropyPaymentLevel : ProofLevel
p11CanonicalEntropyPaymentLevel = conditional
