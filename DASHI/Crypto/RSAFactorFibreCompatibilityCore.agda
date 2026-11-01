module DASHI.Crypto.RSAFactorFibreCompatibilityCore where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

------------------------------------------------------------------------
-- Generic local multiplicative-fibre compatibility.
--
-- For every multiplicative group, every candidate unit x admits a compatible
-- complement x⁻¹ · n whose product with x is n. Hence a local test that asks
-- only whether a candidate residue can be completed to the public product is
-- constant on all units: it cannot separate the hidden factor fibre.
------------------------------------------------------------------------

record MultiplicativeGroup (ℓ : Level) : Set (lsuc ℓ) where
  infixl 7 _∙_
  field
    Carrier : Set ℓ
    _∙_ : Carrier → Carrier → Carrier
    ε : Carrier
    inv : Carrier → Carrier
    assoc : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
    leftIdentity : ∀ x → ε ∙ x ≡ x
    rightInverse : ∀ x → x ∙ inv x ≡ ε

open MultiplicativeGroup public

compatibleComplement :
  ∀ {ℓ} →
  (G : MultiplicativeGroup ℓ) →
  Carrier G →
  Carrier G →
  Carrier G
compatibleComplement G publicProduct candidate =
  _∙_ G (inv G candidate) publicProduct

candidateTimesCompatibleComplement :
  ∀ {ℓ} →
  (G : MultiplicativeGroup ℓ) →
  (publicProduct candidate : Carrier G) →
  _∙_ G candidate (compatibleComplement G publicProduct candidate)
  ≡
  publicProduct
candidateTimesCompatibleComplement G publicProduct candidate =
  trans
    (sym (assoc G candidate (inv G candidate) publicProduct))
    (trans
      (cong
        (λ t → _∙_ G t publicProduct)
        (rightInverse G candidate))
      (leftIdentity G publicProduct))

record LocalProductCompatibilityWitness
    {ℓ}
    (G : MultiplicativeGroup ℓ)
    (publicProduct candidate : Carrier G) :
    Set ℓ where
  constructor mkLocalProductCompatibilityWitness
  field
    complement : Carrier G
    productMatchesPublicSurface :
      _∙_ G candidate complement ≡ publicProduct

open LocalProductCompatibilityWitness public

localProductCompatibilityWitness :
  ∀ {ℓ} →
  (G : MultiplicativeGroup ℓ) →
  (publicProduct candidate : Carrier G) →
  LocalProductCompatibilityWitness G publicProduct candidate
localProductCompatibilityWitness G publicProduct candidate =
  mkLocalProductCompatibilityWitness
    (compatibleComplement G publicProduct candidate)
    (candidateTimesCompatibleComplement G publicProduct candidate)

------------------------------------------------------------------------
-- The non-separation theorem in the exact form needed by the RSA bridge.
------------------------------------------------------------------------

record LocalCompatibilityNonSeparation
    {ℓ}
    (G : MultiplicativeGroup ℓ)
    (publicProduct : Carrier G) :
    Set (lsuc ℓ) where
  constructor mkLocalCompatibilityNonSeparation
  field
    everyCandidateHasCompatibleComplement :
      (candidate : Carrier G) →
      LocalProductCompatibilityWitness G publicProduct candidate

open LocalCompatibilityNonSeparation public

localCompatibilityIsNonSeparating :
  ∀ {ℓ} →
  (G : MultiplicativeGroup ℓ) →
  (publicProduct : Carrier G) →
  LocalCompatibilityNonSeparation G publicProduct
localCompatibilityIsNonSeparating G publicProduct =
  mkLocalCompatibilityNonSeparation
    (localProductCompatibilityWitness G publicProduct)
