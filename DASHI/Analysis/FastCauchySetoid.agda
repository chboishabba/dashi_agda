module DASHI.Analysis.FastCauchySetoid where

open import Level using (0ℓ)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)

open import DASHI.Analysis.FastCauchyReals

fastCauchyIsEquivalence :
  ∀ (A : RationalMetricAuthority) →
  IsEquivalence (_≈R_ {A})
fastCauchyIsEquivalence A =
  record
    { refl = reflexive (canonicalFastCauchyEqualityLaws A)
    ; sym = symmetric (canonicalFastCauchyEqualityLaws A)
    ; trans = transitive (canonicalFastCauchyEqualityLaws A)
    }

fastCauchySetoid :
  RationalMetricAuthority →
  Setoid 0ℓ 0ℓ
fastCauchySetoid A =
  record
    { Carrier = FastCauchyReal A
    ; _≈_ = _≈R_
    ; isEquivalence = fastCauchyIsEquivalence A
    }
