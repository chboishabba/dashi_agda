module DASHI.Physics.YangMills.BalabanClayGate4WilsonBoltzmannSuppressionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4LiteralWilsonLargeFieldPredicateExact as Wilson

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. I. The Basic Step of the R Operation",
-- Communications in Mathematical Physics 122 (1989), 175--202.
-- DOI: 10.1007/BF01257412.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- This module proves only order-algebra consequences of the existing literal
-- SU(2) Wilson-cost theorem. It does not identify the resulting local threshold
-- with Bałaban's complete T-operation constant without an explicit convention
-- and measure-density bridge.
------------------------------------------------------------------------

record ExponentialBoltzmannOrder : Set₁ where
  field
    expNegative : ℚ → ℚ
    boltzmannWeight : ℚ → ℚ
    boltzmannDefinition : ∀ cost →
      boltzmannWeight cost ≡ expNegative cost
    expNegativeAntitone : ∀ {lower upper} →
      lower ≤ upper → expNegative upper ≤ expNegative lower

open ExponentialBoltzmannOrder public

largePlaquetteImpliesBoltzmannSuppression :
  ∀ {Scale Configuration Gauge Block Plaquette}
    {largeField : Wilson.LiteralWilsonLargeFieldData
      Scale Configuration Gauge Block Plaquette}
    (cost : Wilson.LiteralWilsonCostData largeField)
    (exponential : ExponentialBoltzmannOrder)
    scale configuration plaquette →
  Wilson.LargePlaquette largeField scale configuration plaquette →
  boltzmannWeight exponential
    (Wilson.scaledWilsonPlaquetteCost cost scale configuration plaquette)
  ≤ expNegative exponential
      ((DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact.halfℚ
        * Wilson.beta cost scale)
        * DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact.squareℚ
          (Wilson.threshold largeField scale))
largePlaquetteImpliesBoltzmannSuppression cost exponential
  scale configuration plaquette large =
  subst
    (λ left → left ≤ expNegative exponential
      ((DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact.halfℚ
        * Wilson.beta cost scale)
        * DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact.squareℚ
          (Wilson.threshold _ scale)))
    (sym (boltzmannDefinition exponential
      (Wilson.scaledWilsonPlaquetteCost cost scale configuration plaquette)))
    (expNegativeAntitone exponential
      (Wilson.largePlaquetteImpliesWilsonCost cost
        scale configuration plaquette large))

record OrderedPlaquetteProduct (Plaquette : Set) : Set₁ where
  field
    Weight : Set
    zero one : Weight
    multiply : Weight → Weight → Weight
    LessEqual : Weight → Weight → Set

    weight : Plaquette → Weight
    suppression : Weight

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    multiplyNonnegative : ∀ {left right} →
      LessEqual zero left → LessEqual zero right →
      LessEqual zero (multiply left right)
    multiplyMonotoneNonnegative :
      ∀ {left leftUpper right rightUpper} →
      LessEqual zero left → LessEqual zero leftUpper →
      LessEqual zero right → LessEqual zero rightUpper →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (multiply left right) (multiply leftUpper rightUpper)

    weightNonnegative : ∀ plaquette → LessEqual zero (weight plaquette)
    weightBelowOne : ∀ plaquette → LessEqual (weight plaquette) one
    oneNonnegative : LessEqual zero one
    suppressionNonnegative : LessEqual zero suppression
    multiplyOneRight : ∀ value → multiply value one ≡ value
    multiplyOneLeft : ∀ value → multiply one value ≡ value

open OrderedPlaquetteProduct public

productWeights :
  ∀ {Plaquette} → OrderedPlaquetteProduct Plaquette → List Plaquette →
  Weight
productWeights dataSet [] = one dataSet
productWeights dataSet (plaquette ∷ plaquettes) =
  multiply dataSet (weight dataSet plaquette) (productWeights dataSet plaquettes)

productWeightsNonnegative :
  ∀ {Plaquette} (dataSet : OrderedPlaquetteProduct Plaquette) plaquettes →
  LessEqual dataSet (zero dataSet) (productWeights dataSet plaquettes)
productWeightsNonnegative dataSet [] = oneNonnegative dataSet
productWeightsNonnegative dataSet (plaquette ∷ plaquettes) =
  multiplyNonnegative dataSet
    (weightNonnegative dataSet plaquette)
    (productWeightsNonnegative dataSet plaquettes)

productWeightsBelowOne :
  ∀ {Plaquette} (dataSet : OrderedPlaquetteProduct Plaquette) plaquettes →
  LessEqual dataSet (productWeights dataSet plaquettes) (one dataSet)
productWeightsBelowOne dataSet [] = reflexive dataSet (one dataSet)
productWeightsBelowOne dataSet (plaquette ∷ plaquettes) =
  subst
    (λ upper → LessEqual dataSet
      (multiply dataSet (weight dataSet plaquette)
        (productWeights dataSet plaquettes)) upper)
    (multiplyOneLeft dataSet (one dataSet))
    (multiplyMonotoneNonnegative dataSet
      (weightNonnegative dataSet plaquette)
      (oneNonnegative dataSet)
      (productWeightsNonnegative dataSet plaquettes)
      (oneNonnegative dataSet)
      (weightBelowOne dataSet plaquette)
      (productWeightsBelowOne dataSet plaquettes))

oneSuppressedFactorControlsProduct :
  ∀ {Plaquette} (dataSet : OrderedPlaquetteProduct Plaquette)
    {selected plaquettes} →
  Wilson._∈_ selected plaquettes →
  LessEqual dataSet (weight dataSet selected) (suppression dataSet) →
  LessEqual dataSet (productWeights dataSet plaquettes) (suppression dataSet)
oneSuppressedFactorControlsProduct dataSet Wilson.here selectedSuppressed =
  subst
    (λ upper → LessEqual dataSet
      (multiply dataSet (weight dataSet _) (productWeights dataSet _)) upper)
    (multiplyOneRight dataSet (suppression dataSet))
    (multiplyMonotoneNonnegative dataSet
      (weightNonnegative dataSet _)
      (suppressionNonnegative dataSet)
      (productWeightsNonnegative dataSet _)
      (oneNonnegative dataSet)
      selectedSuppressed
      (productWeightsBelowOne dataSet _))
oneSuppressedFactorControlsProduct dataSet
  (Wilson.there membership) selectedSuppressed =
  subst
    (λ upper → LessEqual dataSet
      (multiply dataSet (weight dataSet _) (productWeights dataSet _)) upper)
    (multiplyOneLeft dataSet (suppression dataSet))
    (multiplyMonotoneNonnegative dataSet
      (weightNonnegative dataSet _)
      (oneNonnegative dataSet)
      (productWeightsNonnegative dataSet _)
      (suppressionNonnegative dataSet)
      (weightBelowOne dataSet _)
      (oneSuppressedFactorControlsProduct dataSet membership selectedSuppressed))

record LargeBlockOwnedBoltzmannProduct
    {Scale Configuration Gauge Block Plaquette : Set}
    (largeField : Wilson.LiteralWilsonLargeFieldData
      Scale Configuration Gauge Block Plaquette) : Set₁ where
  field
    productData : OrderedPlaquetteProduct Plaquette
    plaquetteWeightMeaning :
      ∀ scale configuration plaquette →
      weight productData plaquette ≡
      weight productData plaquette

open LargeBlockOwnedBoltzmannProduct public

largeFieldBlockHasOwnedSuppression :
  ∀ {Scale Configuration Gauge Block Plaquette}
    {largeField : Wilson.LiteralWilsonLargeFieldData
      Scale Configuration Gauge Block Plaquette}
    (productData : OrderedPlaquetteProduct Plaquette)
    scale configuration block →
  Wilson.LargeFieldBlock largeField scale configuration block →
  (∀ plaquette →
    Wilson.LargePlaquette largeField scale configuration plaquette →
    LessEqual productData (weight productData plaquette)
      (suppression productData)) →
  LessEqual productData
    (productWeights productData (Wilson.ownedPlaquettes largeField block))
    (suppression productData)
largeFieldBlockHasOwnedSuppression productData scale configuration block
  (Wilson.largeWitness plaquette member large) localSuppression =
  oneSuppressedFactorControlsProduct productData member
    (localSuppression plaquette large)

localWilsonBoltzmannSuppressionAssemblyLevel : ProofLevel
localWilsonBoltzmannSuppressionAssemblyLevel = machineChecked

ownedPlaquetteProductSuppressionLevel : ProofLevel
ownedPlaquetteProductSuppressionLevel = machineChecked

-- Remaining physical identification: the T-operation density's action factor
-- must equal this owned-plaquette Boltzmann product, with all Jacobian,
-- determinant, localization and patch factors assigned to their existing owners.
tOperationActionFactorIdentificationInputsLevel : ProofLevel
tOperationActionFactorIdentificationInputsLevel = conditional
