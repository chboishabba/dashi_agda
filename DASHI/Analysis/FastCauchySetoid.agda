module DASHI.Analysis.FastCauchySetoid where

open import Level using (0ℓ)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)

open import DASHI.Analysis.FastCauchyReals

fastCauchyIsEquivalence :
  ∀ (A : RationalMetricAuthority) →
  IsEquivalence (_≈R_ {A})
IsEquivalence.refl (fastCauchyIsEquivalence A) {x} =
  reflexive (canonicalFastCauchyEqualityLaws A) x
IsEquivalence.sym (fastCauchyIsEquivalence A) {x} {y} xy =
  symmetric (canonicalFastCauchyEqualityLaws A) {x} {y} xy
IsEquivalence.trans (fastCauchyIsEquivalence A) {x} {y} {z} xy yz =
  transitive (canonicalFastCauchyEqualityLaws A) {x} {y} {z} xy yz

fastCauchySetoid :
  RationalMetricAuthority →
  Setoid 0ℓ 0ℓ
fastCauchySetoid A =
  record
    { Carrier = FastCauchyReal A
    ; _≈_ = _≈R_
    ; isEquivalence = fastCauchyIsEquivalence A
    }
