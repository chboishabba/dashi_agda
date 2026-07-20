module DASHI.Physics.Closure.ShiftFiniteNormedTangent where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties as NatP using (≤-refl)

open import DASHI.Physics.Closure.ShiftFiniteTangentSemigroup as Tangent
open import DASHI.Physics.Closure.ShiftFiniteScalingFusionWard as Finite

------------------------------------------------------------------------
-- Exact additive/normed algebra on the finite perturbation carrier.
--
-- Addition is the existing pointed fusion/join.  It is commutative,
-- associative, idempotent, and has zeroPerturbation as unit.  The norm is the
-- existing finite scaling rank 2,1,0.  The induced derivative preserves the
-- addition and does not increase the norm.
--
-- This is a normed idempotent commutative monoid, not a vector space: there are
-- no additive inverses, scalar field, homogeneity theorem, or Banach topology.

infixl 6 _⊕t_

_⊕t_ :
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation
_⊕t_ = Finite._⊗p_

finiteNorm : Tangent.ShiftFinitePerturbation → Nat
finiteNorm = Finite.finiteScalingDimension

addLeftUnit :
  (p : Tangent.ShiftFinitePerturbation) →
  Tangent.zeroPerturbation ⊕t p ≡ p
addLeftUnit = Finite.fusionLeftUnit

addRightUnit :
  (p : Tangent.ShiftFinitePerturbation) →
  p ⊕t Tangent.zeroPerturbation ≡ p
addRightUnit = Finite.fusionRightUnit

addAssociative :
  (p q r : Tangent.ShiftFinitePerturbation) →
  (p ⊕t q) ⊕t r ≡ p ⊕t (q ⊕t r)
addAssociative = Finite.fusionAssociative

addCommutative :
  (p q : Tangent.ShiftFinitePerturbation) →
  p ⊕t q ≡ q ⊕t p
addCommutative Tangent.startPerturbation Tangent.startPerturbation = refl
addCommutative Tangent.startPerturbation Tangent.nextPerturbation = refl
addCommutative Tangent.startPerturbation Tangent.zeroPerturbation = refl
addCommutative Tangent.nextPerturbation Tangent.startPerturbation = refl
addCommutative Tangent.nextPerturbation Tangent.nextPerturbation = refl
addCommutative Tangent.nextPerturbation Tangent.zeroPerturbation = refl
addCommutative Tangent.zeroPerturbation Tangent.startPerturbation = refl
addCommutative Tangent.zeroPerturbation Tangent.nextPerturbation = refl
addCommutative Tangent.zeroPerturbation Tangent.zeroPerturbation = refl

addIdempotent :
  (p : Tangent.ShiftFinitePerturbation) →
  p ⊕t p ≡ p
addIdempotent = Finite.fusionIdempotent

normZero : finiteNorm Tangent.zeroPerturbation ≡ zero
normZero = refl

normTriangle :
  (p q : Tangent.ShiftFinitePerturbation) →
  finiteNorm (p ⊕t q) ≤ finiteNorm p + finiteNorm q
normTriangle Tangent.startPerturbation Tangent.startPerturbation =
  s≤s (s≤s z≤n)
normTriangle Tangent.startPerturbation Tangent.nextPerturbation =
  s≤s (s≤s z≤n)
normTriangle Tangent.startPerturbation Tangent.zeroPerturbation =
  NatP.≤-refl
normTriangle Tangent.nextPerturbation Tangent.startPerturbation =
  s≤s (s≤s z≤n)
normTriangle Tangent.nextPerturbation Tangent.nextPerturbation =
  s≤s z≤n
normTriangle Tangent.nextPerturbation Tangent.zeroPerturbation =
  NatP.≤-refl
normTriangle Tangent.zeroPerturbation Tangent.startPerturbation =
  NatP.≤-refl
normTriangle Tangent.zeroPerturbation Tangent.nextPerturbation =
  NatP.≤-refl
normTriangle Tangent.zeroPerturbation Tangent.zeroPerturbation =
  z≤n

derivativeAdditive :
  (p q : Tangent.ShiftFinitePerturbation) →
  Tangent.finiteDerivativeStep (p ⊕t q)
    ≡
  Tangent.finiteDerivativeStep p ⊕t Tangent.finiteDerivativeStep q
derivativeAdditive Tangent.startPerturbation Tangent.startPerturbation = refl
derivativeAdditive Tangent.startPerturbation Tangent.nextPerturbation = refl
derivativeAdditive Tangent.startPerturbation Tangent.zeroPerturbation = refl
derivativeAdditive Tangent.nextPerturbation Tangent.startPerturbation = refl
derivativeAdditive Tangent.nextPerturbation Tangent.nextPerturbation = refl
derivativeAdditive Tangent.nextPerturbation Tangent.zeroPerturbation = refl
derivativeAdditive Tangent.zeroPerturbation Tangent.startPerturbation = refl
derivativeAdditive Tangent.zeroPerturbation Tangent.nextPerturbation = refl
derivativeAdditive Tangent.zeroPerturbation Tangent.zeroPerturbation = refl

derivativeNormNonIncreasing :
  (p : Tangent.ShiftFinitePerturbation) →
  finiteNorm (Tangent.finiteDerivativeStep p) ≤ finiteNorm p
derivativeNormNonIncreasing Tangent.startPerturbation = s≤s z≤n
derivativeNormNonIncreasing Tangent.nextPerturbation = z≤n
derivativeNormNonIncreasing Tangent.zeroPerturbation = NatP.≤-refl

record ShiftFiniteNormedTangent : Setω where
  field
    TangentCarrier : Set
    zeroTangent : TangentCarrier
    add : TangentCarrier → TangentCarrier → TangentCarrier
    norm : TangentCarrier → Nat
    derivative : TangentCarrier → TangentCarrier

    leftUnit : (p : TangentCarrier) → add zeroTangent p ≡ p
    rightUnit : (p : TangentCarrier) → add p zeroTangent ≡ p
    associative :
      (p q r : TangentCarrier) →
      add (add p q) r ≡ add p (add q r)
    commutative :
      (p q : TangentCarrier) →
      add p q ≡ add q p
    idempotent : (p : TangentCarrier) → add p p ≡ p

    zeroNorm : norm zeroTangent ≡ zero
    triangle :
      (p q : TangentCarrier) →
      norm (add p q) ≤ norm p + norm q

    derivativePreservesAdd :
      (p q : TangentCarrier) →
      derivative (add p q) ≡ add (derivative p) (derivative q)
    derivativeNonExpansive :
      (p : TangentCarrier) →
      norm (derivative p) ≤ norm p

    nonClaimBoundary : List String

open ShiftFiniteNormedTangent public

canonicalShiftFiniteNormedTangent : ShiftFiniteNormedTangent
canonicalShiftFiniteNormedTangent =
  record
    { TangentCarrier = Tangent.ShiftFinitePerturbation
    ; zeroTangent = Tangent.zeroPerturbation
    ; add = _⊕t_
    ; norm = finiteNorm
    ; derivative = Tangent.finiteDerivativeStep
    ; leftUnit = addLeftUnit
    ; rightUnit = addRightUnit
    ; associative = addAssociative
    ; commutative = addCommutative
    ; idempotent = addIdempotent
    ; zeroNorm = normZero
    ; triangle = normTriangle
    ; derivativePreservesAdd = derivativeAdditive
    ; derivativeNonExpansive = derivativeNormNonIncreasing
    ; nonClaimBoundary =
        "ShiftFiniteNormedTangent is an exact finite normed idempotent commutative monoid"
        ∷ "the additive operation is the existing pointed fusion/join"
        ∷ "the norm is the existing finite 2,1,0 scaling/collapse rank"
        ∷ "the exact induced derivative preserves addition and is norm non-increasing"
        ∷ "No additive inverses, scalar field, vector space, inner product, Banach norm, or Frechet derivative is claimed"
        ∷ []
    }
