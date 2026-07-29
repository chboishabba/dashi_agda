module DASHI.Physics.YangMills.BalabanClayGate4PhysicalTDensityIdentificationExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)
open import Data.Rational using (ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

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
    ownedPlaquettes : Component → SlowField → Fine → Agda.Builtin.List.List Plaquette

    actionFactorIsOwnedPlaquetteProduct : ∀ scale component slow fine →
      Six.actionFactor (sixFactors identification) scale
        (traversalOf identification component slow fine)
      ≡ Wilson.productWeights productData (ownedPlaquettes component slow fine)

    jacobianOwnerIsExisting : ∀ scale component slow fine →
      Six.jacobianFactor (sixFactors identification) scale
        (traversalOf identification component slow fine)
      ≡ Six.jacobianFactor (sixFactors identification) scale
          (traversalOf identification component slow fine)

    determinantOwnerIsExisting : ∀ scale component slow fine →
      Six.determinantFactor (sixFactors identification) scale
        (traversalOf identification component slow fine)
      ≡ Six.determinantFactor (sixFactors identification) scale
          (traversalOf identification component slow fine)

    localizationAndPatchOwnersAreExisting : ∀ scale component slow fine →
      Six.localizationFactor (sixFactors identification) scale
        (traversalOf identification component slow fine)
      ≡ Six.localizationFactor (sixFactors identification) scale
          (traversalOf identification component slow fine)

open OwnedPlaquetteActionFactorIdentification public

physicalTDensityExistingSixFactorLevel : ProofLevel
physicalTDensityExistingSixFactorLevel = machineChecked

physicalTDensityOneSixteenthLevel : ProofLevel
physicalTDensityOneSixteenthLevel = machineChecked

ownedPlaquetteActionIdentificationVocabularyLevel : ProofLevel
ownedPlaquetteActionIdentificationVocabularyLevel = machineChecked

-- The concrete inhabitant must identify the actual fast field with the traversal
-- used by the existing six-factor producer and identify its action factor with
-- the bond-derived owned-plaquette product.  Jacobian, determinant,
-- localization and patch estimates are then reused rather than reproved.
physicalFastFieldTraversalIdentificationInputsLevel : ProofLevel
physicalFastFieldTraversalIdentificationInputsLevel = conditional

ownedPlaquetteProductActionMeaningInputsLevel : ProofLevel
ownedPlaquetteProductActionMeaningInputsLevel = conditional
