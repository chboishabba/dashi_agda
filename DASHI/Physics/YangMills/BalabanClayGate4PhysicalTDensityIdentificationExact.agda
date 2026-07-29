module DASHI.Physics.YangMills.BalabanClayGate4PhysicalTDensityIdentificationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Data.Rational using (ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayP3FiniteConstrainedIntegralExact as Integral
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanClayT2LiteralWilsonSixFactorProducerExact as Six
import DASHI.Physics.YangMills.BalabanClayT2WilsonActivityFactorProductExact as Product
import DASHI.Physics.YangMills.BalabanClayGate4WilsonBoltzmannSuppressionExact as Wilson

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
-- Project Euclid stable identifier: euclid:cmp/1104161193.
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
------------------------------------------------------------------------

record PhysicalTConstruction
    (Scale Fine SlowField Component Functional : Set) : Set₁ where
  field
    sumData : Integral.FiniteConstrainedSum Fine SlowField ℚ
    classData : T.ComponentClassData Scale Component

    Traversal : Set
    sixFactors : Six.LiteralWilsonSixFactorData Scale Traversal
    traversalOf : Component → SlowField → Fine → Traversal

    fastFibre : Scale → Component → List Fine
    evaluateFunctional : Functional → Fine → ℚ
    multiply : ℚ → ℚ → ℚ
    oneFunctional : Functional
    largeFieldIndicator : Scale → Component → Functional

open PhysicalTConstruction public

physicalTData :
  ∀ {Scale Fine SlowField Component Functional} →
  PhysicalTConstruction Scale Fine SlowField Component Functional →
  T.FiniteLocalTOperationData Scale Fine SlowField Component Functional ℚ
physicalTData construction = record
  { T.FiniteLocalTOperationData.sumData = sumData construction
  ; T.FiniteLocalTOperationData.classData = classData construction
  ; T.FiniteLocalTOperationData.fastFibre = fastFibre construction
  ; T.FiniteLocalTOperationData.localDensity = λ scale component slow fine →
      Six.activity (sixFactors construction) scale
        (traversalOf construction component slow fine)
  ; T.FiniteLocalTOperationData.evaluateFunctional =
      evaluateFunctional construction
  ; T.FiniteLocalTOperationData.multiply = multiply construction
  ; T.FiniteLocalTOperationData.oneFunctional = oneFunctional construction
  ; T.FiniteLocalTOperationData.largeFieldIndicator =
      largeFieldIndicator construction
  }

record PhysicalTDensityIdentification
    {Scale Fine SlowField Component Functional : Set}
    (dataSet : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ) : Set₁ where
  field
    Traversal : Set
    sixFactors : Six.LiteralWilsonSixFactorData Scale Traversal
    traversalOf : Component → SlowField → Fine → Traversal

    densityIsExistingActivity : ∀ scale component slow fine →
      T.localDensity dataSet scale component slow fine
      ≡ Six.activity sixFactors scale (traversalOf component slow fine)

open PhysicalTDensityIdentification public

physicalTDensityIdentificationFromConstruction :
  ∀ {Scale Fine SlowField Component Functional}
    (construction : PhysicalTConstruction
      Scale Fine SlowField Component Functional) →
  PhysicalTDensityIdentification (physicalTData construction)
physicalTDensityIdentificationFromConstruction construction = record
  { PhysicalTDensityIdentification.Traversal = Traversal construction
  ; PhysicalTDensityIdentification.sixFactors = sixFactors construction
  ; PhysicalTDensityIdentification.traversalOf = traversalOf construction
  ; PhysicalTDensityIdentification.densityIsExistingActivity =
      λ scale component slow fine → refl
  }

physicalTDensityBelowOneSixteenth :
  ∀ {Scale Fine SlowField Component Functional}
    {dataSet : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ}
    (identification : PhysicalTDensityIdentification dataSet)
    scale component slow fine →
  T.localDensity dataSet scale component slow fine ≤ Product.oneSixteenth
physicalTDensityBelowOneSixteenth identification scale component slow fine =
  subst
    (λ lower → lower ≤ Product.oneSixteenth)
    (sym (densityIsExistingActivity identification scale component slow fine))
    (Six.literalWilsonActivityPerTraversalBelowOneSixteenth
      (sixFactors identification) scale
      (traversalOf identification component slow fine))

record OwnedPlaquetteActionFactorIdentification
    {Scale Fine SlowField Component Functional Plaquette : Set}
    (dataSet : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ)
    (identification : PhysicalTDensityIdentification dataSet) : Set₁ where
  field
    productData : Wilson.OrderedPlaquetteProduct Plaquette
    interpretProductWeight : Wilson.Weight productData → ℚ
    ownedPlaquettes : Component → SlowField → Fine → List Plaquette

    actionFactorIsOwnedPlaquetteProduct : ∀ scale component slow fine →
      Six.actionFactor (sixFactors identification) scale
        (traversalOf identification component slow fine)
      ≡ interpretProductWeight
          (Wilson.productWeights productData
            (ownedPlaquettes component slow fine))

    physicalJacobian physicalDeterminant physicalLocalization physicalPatch :
      Scale → Component → SlowField → Fine → ℚ

    jacobianOwnerIsExisting : ∀ scale component slow fine →
      physicalJacobian scale component slow fine
      ≡ Six.jacobianFactor (sixFactors identification) scale
          (traversalOf identification component slow fine)

    determinantOwnerIsExisting : ∀ scale component slow fine →
      physicalDeterminant scale component slow fine
      ≡ Six.determinantFactor (sixFactors identification) scale
          (traversalOf identification component slow fine)

    localizationOwnerIsExisting : ∀ scale component slow fine →
      physicalLocalization scale component slow fine
      ≡ Six.localizationFactor (sixFactors identification) scale
          (traversalOf identification component slow fine)

    patchOwnerIsExisting : ∀ scale component slow fine →
      physicalPatch scale component slow fine
      ≡ Six.patchFactor (sixFactors identification) scale
          (traversalOf identification component slow fine)

open OwnedPlaquetteActionFactorIdentification public

physicalTConstructionLevel : ProofLevel
physicalTConstructionLevel = machineChecked

physicalTDensityExistingSixFactorLevel : ProofLevel
physicalTDensityExistingSixFactorLevel = machineChecked

physicalTDensityOneSixteenthLevel : ProofLevel
physicalTDensityOneSixteenthLevel = machineChecked

ownedPlaquetteActionIdentificationVocabularyLevel : ProofLevel
ownedPlaquetteActionIdentificationVocabularyLevel = machineChecked

physicalFastFieldTraversalIdentificationInputsLevel : ProofLevel
physicalFastFieldTraversalIdentificationInputsLevel = conditional

ownedPlaquetteProductActionMeaningInputsLevel : ProofLevel
ownedPlaquetteProductActionMeaningInputsLevel = conditional
