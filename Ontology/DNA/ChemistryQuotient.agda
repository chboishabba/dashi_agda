module Ontology.DNA.ChemistryQuotient where

open import Agda.Builtin.Bool     using (Bool; true; false)
open import Agda.Builtin.Nat      using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma    using (Σ; _,_)
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import Ontology.DNA.Supervoxel4Adic using
  (Base; A; C; G; T; FlatDNA256)
import Ontology.Hecke.QuotientRepresentation as HQ

------------------------------------------------------------------------
-- Chemistry quotient surface for a DNA256 supervoxel:
-- the feature map keeps chemistry-visible structure, and the thermo-kernel
-- is a scalar screen over candidate states.

data Strength : Set where
  weak strong : Strength

data PurineClass : Set where
  pyrimidine purine : PurineClass

strength : Base → Strength
strength A = weak
strength T = weak
strength C = strong
strength G = strong

purineClass : Base → PurineClass
purineClass A = purine
purineClass G = purine
purineClass C = pyrimidine
purineClass T = pyrimidine

FeatureU : Set
FeatureU = Vec Strength 256

FeatureV : Set
FeatureV = Vec PurineClass 256

record ChemistryFeature : Set where
  constructor chemistryFeature
  field
    u : FeatureU
    v : FeatureV

record ChemistryQuotient : Set₁ where
  field
    featureMap : FlatDNA256 → ChemistryFeature
    thermoKernel : FlatDNA256 → Nat
    admissible : FlatDNA256 → Bool

  _≈chem_ : FlatDNA256 → FlatDNA256 → Set
  x ≈chem y = featureMap x ≡ featureMap y

record ChemistryQuotientInterface : Set₁ where
  field
    quotient : ChemistryQuotient
    representative : ChemistryFeature → FlatDNA256
    section :
      ∀ f →
      ChemistryQuotient.featureMap quotient (representative f) ≡ f

  equivalence : HQ.EquivalenceOn FlatDNA256
  equivalence = record
    { _≈_   = ChemistryQuotient._≈chem_ quotient
    ; refl  = λ x → refl
    ; sym   = sym
    ; trans = trans
    }

  interface : HQ.QuotientInterfaceOn FlatDNA256 ChemistryFeature
  interface = record
    { equiv          = equivalence
    ; proj           = ChemistryQuotient.featureMap quotient
    ; respect-proj   = λ eq → eq
    ; representative = representative
    ; section        = section
    }
