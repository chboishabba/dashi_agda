module DASHI.Physics.YangMills.BalabanClayGate4FlatWilsonActionPositivityExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong₂; subst; sym; trans)

open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4WilsonBoltzmannSuppressionExact as Wilson

------------------------------------------------------------------------
-- Primary provenance.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Michael Creutz,
-- "Quarks, Gluons and Lattices", Cambridge University Press, open-access
-- reissue (2022). DOI: 10.1017/9781009290395.
--
-- At the canonical flat connection every plaquette holonomy is the identity,
-- its Wilson cost is zero, and its Boltzmann weight is one. The exact theorem
-- below isolates the remaining representation premise as `flatWeightOne` and
-- proves the complete owned-plaquette product is one and strictly positive.
------------------------------------------------------------------------

record FlatWilsonProductData (Plaquette : Set) : Set₁ where
  field
    productData : Wilson.OrderedPlaquetteProduct Plaquette
    flatPlaquettes : List Plaquette

    flatWeightOne : ∀ (plaquette : Plaquette) →
      plaquette ∈ flatPlaquettes →
      Wilson.weight productData plaquette ≡ Wilson.one productData

    Positive : Wilson.Weight productData → Set
    onePositive : Positive (Wilson.one productData)
    multiplyPositive : ∀ {left right} →
      Positive left → Positive right →
      Positive (Wilson.multiply productData left right)

open FlatWilsonProductData public

flatProductExactOnList :
  ∀ {Plaquette}
    (dataSet : FlatWilsonProductData Plaquette)
    (plaquettes : List Plaquette) →
  (∀ (plaquette : Plaquette) → plaquette ∈ plaquettes →
    Wilson.weight (productData dataSet) plaquette
    ≡ Wilson.one (productData dataSet)) →
  Wilson.productWeights (productData dataSet) plaquettes
  ≡ Wilson.one (productData dataSet)
flatProductExactOnList dataSet [] allOne = refl
flatProductExactOnList dataSet (plaquette ∷ plaquettes) allOne =
  trans
    (cong₂ (Wilson.multiply (productData dataSet))
      (allOne plaquette here)
      (flatProductExactOnList dataSet plaquettes
        (λ selected membership →
          allOne selected (there membership))))
    (Wilson.multiplyOneLeft (productData dataSet)
      (Wilson.one (productData dataSet)))

flatOwnedPlaquetteProductExact :
  ∀ {Plaquette} (dataSet : FlatWilsonProductData Plaquette) →
  Wilson.productWeights (productData dataSet) (flatPlaquettes dataSet)
  ≡ Wilson.one (productData dataSet)
flatOwnedPlaquetteProductExact dataSet =
  flatProductExactOnList dataSet (flatPlaquettes dataSet)
    (flatWeightOne dataSet)

flatOwnedPlaquetteProductPositive :
  ∀ {Plaquette} (dataSet : FlatWilsonProductData Plaquette) →
  Positive dataSet
    (Wilson.productWeights (productData dataSet) (flatPlaquettes dataSet))
flatOwnedPlaquetteProductPositive dataSet =
  subst (Positive dataSet)
    (sym (flatOwnedPlaquetteProductExact dataSet))
    (onePositive dataSet)

flatWilsonProductExactLevel : ProofLevel
flatWilsonProductExactLevel = machineChecked

flatWilsonProductPositivityLevel : ProofLevel
flatWilsonProductPositivityLevel = machineChecked

physicalFlatPlaquetteBoltzmannOneInputsLevel : ProofLevel
physicalFlatPlaquetteBoltzmannOneInputsLevel = conditional
