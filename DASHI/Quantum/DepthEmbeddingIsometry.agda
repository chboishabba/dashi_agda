module DASHI.Quantum.DepthEmbeddingIsometry where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Unifier using (ℝ; HilbertSpace; toℝ)
open import DASHI.Quantum.Stone using
  (onePointFiniteHilbertSpace; onePointZeroExtensionIota;
   onePointZeroExtensionIota-isometry)

-- Gate 5 concrete packaging of the already-inhabited one-point Stone carrier.
--
-- The depth carrier is the actual one-point Hilbert carrier from Stone.
-- There are no new basis elements in the finite tower, so the "new basis"
-- surface is empty and the embedding/projection are definitional identities.

DepthCarrier : Nat → Set
DepthCarrier _ = HilbertSpace.H onePointFiniteHilbertSpace

BasisAt : Nat → Set
BasisAt _ = ⊤

newBasisAt : Nat → Set
newBasisAt _ = ⊥

innerProduct : (n : Nat) → DepthCarrier n → DepthCarrier n → ℝ
innerProduct _ _ _ = toℝ 1

depthEmbed : (n : Nat) → DepthCarrier n → DepthCarrier (suc n)
depthEmbed _ x = x

depthProject : (n : Nat) → DepthCarrier (suc n) → DepthCarrier n
depthProject _ x = x

depthEmbedIsometry :
  ∀ n (v w : DepthCarrier n) →
  innerProduct (suc n) (depthEmbed n v) (depthEmbed n w)
  ≡
  innerProduct n v w
depthEmbedIsometry _ _ _ = refl

traversalCompat :
  ∀ n (v : DepthCarrier n) (w : DepthCarrier (suc n)) →
  innerProduct (suc n) (depthEmbed n v) w
  ≡
  innerProduct n v (depthProject n w)
traversalCompat _ _ _ = refl

record DepthEmbeddingConcreteWitness : Set₁ where
  field
    carrier :
      Nat → Set

    carrierIsCanonical :
      carrier ≡ DepthCarrier

    basis :
      Nat → Set

    basisIsUnit :
      basis ≡ BasisAt

    newBasis :
      Nat → Set

    newBasisIsEmpty :
      newBasis ≡ newBasisAt

    embedding :
      (n : Nat) → DepthCarrier n → DepthCarrier (suc n)

    embeddingIsCanonical :
      (n : Nat) → (x : DepthCarrier n) → embedding n x ≡ depthEmbed n x

    projection :
      (n : Nat) → DepthCarrier (suc n) → DepthCarrier n

    projectionIsCanonical :
      (n : Nat) → (x : DepthCarrier (suc n)) → projection n x ≡ depthProject n x

    isometryWitness :
      ∀ n (v w : DepthCarrier n) →
      innerProduct (suc n) (embedding n v) (embedding n w)
      ≡
      innerProduct n v w

    traversalWitness :
      ∀ n (v : DepthCarrier n) (w : DepthCarrier (suc n)) →
      innerProduct (suc n) (embedding n v) w
      ≡
      innerProduct n v (projection n w)

    witnessBoundary :
      List String

open DepthEmbeddingConcreteWitness public

canonicalDepthEmbeddingConcreteWitness : DepthEmbeddingConcreteWitness
canonicalDepthEmbeddingConcreteWitness =
  record
    { carrier = DepthCarrier
    ; carrierIsCanonical = refl
    ; basis = BasisAt
    ; basisIsUnit = refl
    ; newBasis = newBasisAt
    ; newBasisIsEmpty = refl
    ; embedding = depthEmbed
    ; embeddingIsCanonical = λ _ _ → refl
    ; projection = depthProject
    ; projectionIsCanonical = λ _ _ → refl
    ; isometryWitness = depthEmbedIsometry
    ; traversalWitness = traversalCompat
    ; witnessBoundary =
        "DepthEmbeddingIsometry packages the actual one-point Stone Hilbert carrier"
        ∷ "The basis is the unique one-point basis and the new-basis surface is empty"
        ∷ "The embedding/projection are definitional identities, so the equalities reduce to refl"
        ∷ []
    }

depthEmbeddingBoundary : List String
depthEmbeddingBoundary =
  "DepthEmbeddingIsometry packages the already-inhabited one-point Stone carrier"
  ∷ "The embedding is the canonical identity on that carrier and there are no new basis elements"
  ∷ []
