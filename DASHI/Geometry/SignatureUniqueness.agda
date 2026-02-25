module DASHI.Geometry.SignatureUniqueness where

open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import DASHI.Geometry.MaskedQuadratic
open import DASHI.Core.Q using (ℚ)

record Cone (V : Set) : Set₁ where
  field
    inside : V → Set

record Arrow (V : Set) : Set₁ where
  field
    tau : V → ℚ
    monotone : Set

record SpatialIsotropy (V : Set) : Set₁ where
  field
    transitive : Set

record SignatureAxioms {n : Nat} : Set₁ where
  field
    MQ : MaskedQuadratic n
    C  : Cone (MaskedQuadratic.V MQ)
    A  : Arrow (MaskedQuadratic.V MQ)
    I  : SpatialIsotropy (MaskedQuadratic.V MQ)

postulate
  SignatureUniqueness31 :
    ∀ {n} (Ax : SignatureAxioms {n}) →
      MaskedQuadratic.signatureTag (SignatureAxioms.MQ Ax) ≡ sig31
