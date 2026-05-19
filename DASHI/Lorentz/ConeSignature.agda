module DASHI.Lorentz.ConeSignature where

open import Agda.Primitive using (Level; lsuc)

record PrincipalSymbol (ℓ : Level) : Set (lsuc ℓ) where
  field
    Covector      : Set ℓ
    characteristic : Covector → Set ℓ
    negativeRegion : Covector → Set ℓ
    nullRegion     : Covector → Set ℓ
    positiveRegion : Covector → Set ℓ

open PrincipalSymbol public

record ConeHypotheses {ℓ : Level} (P : PrincipalSymbol ℓ) : Set (lsuc ℓ) where
  field
    closedCone         : Set ℓ
    convexCone         : Set ℓ
    symmetricCone      : Set ℓ
    nonemptyCone       : Set ℓ
    properCone         : Set ℓ
    nondegenerateSymbol : Set ℓ
    twoNegativeComponents : Set ℓ

open ConeHypotheses public

record LorentzianSignature {ℓ : Level} (P : PrincipalSymbol ℓ) : Set (lsuc ℓ) where
  field
    oneTimelikeDirection : Set ℓ
    spatialHyperplane    : Set ℓ
    coneWitness          : Set ℓ

open LorentzianSignature public

postulate
  cone⇒LorentzSignature :
    ∀ {ℓ : Level} →
    (P : PrincipalSymbol ℓ) →
    ConeHypotheses P →
    LorentzianSignature P
