module DASHI.Physics.Closure.ShiftGF2BanachTangentReference where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.FixedPointAnalyticRGTargets as Targets

------------------------------------------------------------------------
-- A concrete non-Archimedean finite reference tangent.
--
-- GF(2) is used as both scalar and one-dimensional tangent carrier.  With the
-- discrete/trivial valuation it is complete, so this is an honest finite
-- complete valued-field vector model.  It is not an R/C Banach model and is not
-- promoted as the physical tangent space of the shift dynamics.

infixl 6 _⊕₂_
infixl 7 _⊗₂_
infix 4 _≤₂_

_⊕₂_ : Bool → Bool → Bool
false ⊕₂ b = b
true  ⊕₂ false = true
true  ⊕₂ true = false

_⊗₂_ : Bool → Bool → Bool
false ⊗₂ b = false
true  ⊗₂ b = b

neg₂ : Bool → Bool
neg₂ b = b

data _≤₂_ : Bool → Bool → Set where
  false≤ : {b : Bool} → false ≤₂ b
  true≤true : true ≤₂ true

norm₂ : Bool → Bool
norm₂ b = b

distance₂ : Bool → Bool → Bool
distance₂ x y = x ⊕₂ y

addAssoc₂ : (x y z : Bool) → (x ⊕₂ y) ⊕₂ z ≡ x ⊕₂ (y ⊕₂ z)
addAssoc₂ false y z = refl
addAssoc₂ true false z = refl
addAssoc₂ true true z = refl

addComm₂ : (x y : Bool) → x ⊕₂ y ≡ y ⊕₂ x
addComm₂ false false = refl
addComm₂ false true = refl
addComm₂ true false = refl
addComm₂ true true = refl

addUnit₂ : (x : Bool) → false ⊕₂ x ≡ x
addUnit₂ x = refl

addInverse₂ : (x : Bool) → x ⊕₂ neg₂ x ≡ false
addInverse₂ false = refl
addInverse₂ true = refl

mulAssoc₂ : (x y z : Bool) → (x ⊗₂ y) ⊗₂ z ≡ x ⊗₂ (y ⊗₂ z)
mulAssoc₂ false y z = refl
mulAssoc₂ true y z = refl

mulComm₂ : (x y : Bool) → x ⊗₂ y ≡ y ⊗₂ x
mulComm₂ false false = refl
mulComm₂ false true = refl
mulComm₂ true false = refl
mulComm₂ true true = refl

mulUnit₂ : (x : Bool) → true ⊗₂ x ≡ x
mulUnit₂ x = refl

distrib₂ : (a x y : Bool) → a ⊗₂ (x ⊕₂ y) ≡ (a ⊗₂ x) ⊕₂ (a ⊗₂ y)
distrib₂ false x y = refl
distrib₂ true x y = refl

scalarUnit₂ : (x : Bool) → true ⊗₂ x ≡ x
scalarUnit₂ = mulUnit₂

scalarAssoc₂ : (a b x : Bool) → (a ⊗₂ b) ⊗₂ x ≡ a ⊗₂ (b ⊗₂ x)
scalarAssoc₂ = mulAssoc₂

scalarDistributes₂ : (a x y : Bool) → a ⊗₂ (x ⊕₂ y) ≡ (a ⊗₂ x) ⊕₂ (a ⊗₂ y)
scalarDistributes₂ = distrib₂

vectorDistributes₂ : (a b x : Bool) → (a ⊕₂ b) ⊗₂ x ≡ (a ⊗₂ x) ⊕₂ (b ⊗₂ x)
vectorDistributes₂ false b x = refl
vectorDistributes₂ true false false = refl
vectorDistributes₂ true false true = refl
vectorDistributes₂ true true false = refl
vectorDistributes₂ true true true = refl

normZero₂ : norm₂ false ≡ false
normZero₂ = refl

normSeparates₂ : (x : Bool) → norm₂ x ≡ false → x ≡ false
normSeparates₂ false _ = refl
normSeparates₂ true ()

normTriangle₂ : (x y : Bool) → norm₂ (x ⊕₂ y) ≤₂ (norm₂ x ⊕₂ norm₂ y)
normTriangle₂ false false = false≤
normTriangle₂ false true = true≤true
normTriangle₂ true false = true≤true
normTriangle₂ true true = false≤

normHomogeneous₂ : (a x : Bool) → norm₂ (a ⊗₂ x) ≡ a ⊗₂ norm₂ x
normHomogeneous₂ false x = refl
normHomogeneous₂ true x = refl

------------------------------------------------------------------------
-- Discrete completeness.
--
-- On a discrete finite carrier, the relevant Cauchy presentation is eventual
-- constancy.  The witness contains the eventual value and therefore supplies a
-- limit constructively.

record DiscreteCauchy (sequence : Nat → Bool) : Set where
  field
    limit : Bool
    index : Nat
    stable : (n : Nat) → sequence (index + n) ≡ limit

open DiscreteCauchy public

DiscreteConverges : (Nat → Bool) → Bool → Set
DiscreteConverges sequence limit =
  Σ Nat (λ index → (n : Nat) → sequence (index + n) ≡ limit)

discreteComplete :
  (sequence : Nat → Bool) →
  DiscreteCauchy sequence →
  Σ Bool (λ limit → DiscreteConverges sequence limit)
discreteComplete sequence cauchy =
  limit cauchy , (index cauchy , stable cauchy)

------------------------------------------------------------------------
-- Bridge to the generic analytic target surface.

shiftGF2AdditiveNormedTangent :
  Targets.AdditiveNormedTangent Bool Bool
shiftGF2AdditiveNormedTangent =
  record
    { zeroˢ = false
    ; oneˢ = true
    ; _+ˢ_ = _⊕₂_
    ; _*ˢ_ = _⊗₂_
    ; zeroᵀ = false
    ; _+ᵀ_ = _⊕₂_
    ; _·_ = _⊗₂_
    ; norm = norm₂
    ; distance = distance₂
    ; additiveAssociative = addAssoc₂
    ; additiveCommutative = addComm₂
    ; additiveUnit = addUnit₂
    ; scalarUnit = scalarUnit₂
    ; scalarDistributes = scalarDistributes₂
    ; NormAtMost = _≤₂_
    ; normZero = normZero₂
    ; triangle = normTriangle₂
    }

record ShiftGF2BanachTangentReference : Setω where
  field
    tangentTarget : Targets.AdditiveNormedTangent Bool Bool
    additiveInverse : (x : Bool) → x ⊕₂ neg₂ x ≡ false
    scalarAssociative : (a b x : Bool) → (a ⊗₂ b) ⊗₂ x ≡ a ⊗₂ (b ⊗₂ x)
    scalarAddDistributes : (a b x : Bool) → (a ⊕₂ b) ⊗₂ x ≡ (a ⊗₂ x) ⊕₂ (b ⊗₂ x)
    normSeparates : (x : Bool) → norm₂ x ≡ false → x ≡ false
    normHomogeneous : (a x : Bool) → norm₂ (a ⊗₂ x) ≡ a ⊗₂ norm₂ x
    complete :
      (sequence : Nat → Bool) →
      DiscreteCauchy sequence →
      Σ Bool (λ limit → DiscreteConverges sequence limit)
    nonClaimBoundary : List String

open ShiftGF2BanachTangentReference public

canonicalShiftGF2BanachTangentReference :
  ShiftGF2BanachTangentReference
canonicalShiftGF2BanachTangentReference =
  record
    { tangentTarget = shiftGF2AdditiveNormedTangent
    ; additiveInverse = addInverse₂
    ; scalarAssociative = scalarAssoc₂
    ; scalarAddDistributes = vectorDistributes₂
    ; normSeparates = normSeparates₂
    ; normHomogeneous = normHomogeneous₂
    ; complete = discreteComplete
    ; nonClaimBoundary =
        "ShiftGF2BanachTangentReference is a complete one-dimensional vector model over the finite valued field GF(2)"
        ∷ "the completeness theorem uses the exact discrete eventual-constancy Cauchy presentation"
        ∷ "this is a non-Archimedean finite reference model, not an R- or C-valued physical Banach tangent space"
        ∷ "No identification with the three-state idempotent shift tangent is asserted"
        ∷ []
    }
