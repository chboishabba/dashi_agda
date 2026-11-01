module DASHI.Physics.Closure.ShiftFiniteScalingFusionWard where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.DashiDynamicsShiftInstance as DDSI
open import DASHI.Physics.Closure.ShiftFiniteTangentSemigroup as Tangent
open import DASHI.Physics.Closure.ShiftFixedPointPerturbationClassification as Class

------------------------------------------------------------------------
-- Finite scaling-spectrum, fusion-table, and fixed-point Ward surfaces.
--
-- The scaling value is the already-earned held-potential/collapse-depth rank.
-- The fusion law is a finite pointed join table on perturbations.  The Ward
-- identity is the exact invariance of a held insertion under the finite step.
-- None of these is promoted to a continuum scaling dimension, local OPE, or
-- conformal Ward identity.

finiteScalingDimension :
  Tangent.ShiftFinitePerturbation →
  Nat
finiteScalingDimension p =
  DDSI.shiftHeldPotential (Tangent.perturbationState p)

finiteScalingSpectrum : List Nat
finiteScalingSpectrum =
  suc (suc zero)
  ∷ suc zero
  ∷ zero
  ∷ []

finiteScalingStartIs2 :
  finiteScalingDimension Tangent.startPerturbation ≡ suc (suc zero)
finiteScalingStartIs2 = refl

finiteScalingNextIs1 :
  finiteScalingDimension Tangent.nextPerturbation ≡ suc zero
finiteScalingNextIs1 = refl

finiteScalingZeroIs0 :
  finiteScalingDimension Tangent.zeroPerturbation ≡ zero
finiteScalingZeroIs0 = refl

finiteClass :
  Tangent.ShiftFinitePerturbation →
  Class.PerturbationClass
finiteClass p =
  Class.shiftPerturbationClass (Tangent.perturbationState p)

infixl 7 _⊗p_

_⊗p_ :
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation
Tangent.zeroPerturbation ⊗p q = q
p ⊗p Tangent.zeroPerturbation = p
Tangent.startPerturbation ⊗p q = Tangent.startPerturbation
p ⊗p Tangent.startPerturbation = Tangent.startPerturbation
Tangent.nextPerturbation ⊗p Tangent.nextPerturbation = Tangent.nextPerturbation

fusionLeftUnit :
  (p : Tangent.ShiftFinitePerturbation) →
  Tangent.zeroPerturbation ⊗p p ≡ p
fusionLeftUnit p = refl

fusionRightUnit :
  (p : Tangent.ShiftFinitePerturbation) →
  p ⊗p Tangent.zeroPerturbation ≡ p
fusionRightUnit Tangent.startPerturbation = refl
fusionRightUnit Tangent.nextPerturbation = refl
fusionRightUnit Tangent.zeroPerturbation = refl

fusionIdempotent :
  (p : Tangent.ShiftFinitePerturbation) →
  p ⊗p p ≡ p
fusionIdempotent Tangent.startPerturbation = refl
fusionIdempotent Tangent.nextPerturbation = refl
fusionIdempotent Tangent.zeroPerturbation = refl

fusionAssociative :
  (p q r : Tangent.ShiftFinitePerturbation) →
  (p ⊗p q) ⊗p r ≡ p ⊗p (q ⊗p r)
fusionAssociative Tangent.startPerturbation q r = refl
fusionAssociative Tangent.nextPerturbation Tangent.startPerturbation r = refl
fusionAssociative Tangent.nextPerturbation Tangent.nextPerturbation Tangent.startPerturbation = refl
fusionAssociative Tangent.nextPerturbation Tangent.nextPerturbation Tangent.nextPerturbation = refl
fusionAssociative Tangent.nextPerturbation Tangent.nextPerturbation Tangent.zeroPerturbation = refl
fusionAssociative Tangent.nextPerturbation Tangent.zeroPerturbation r = refl
fusionAssociative Tangent.zeroPerturbation q r = refl

finiteTwoPointCorrelation :
  Tangent.ShiftFinitePerturbation →
  Tangent.ShiftFinitePerturbation →
  Nat
finiteTwoPointCorrelation p q =
  finiteScalingDimension p * finiteScalingDimension q

heldInsertionWardLeft :
  (q : Tangent.ShiftFinitePerturbation) →
  finiteTwoPointCorrelation
    (Tangent.finiteDerivativeStep Tangent.zeroPerturbation)
    q
  ≡
  finiteTwoPointCorrelation Tangent.zeroPerturbation q
heldInsertionWardLeft q = refl

heldInsertionWardRight :
  (p : Tangent.ShiftFinitePerturbation) →
  finiteTwoPointCorrelation
    p
    (Tangent.finiteDerivativeStep Tangent.zeroPerturbation)
  ≡
  finiteTwoPointCorrelation p Tangent.zeroPerturbation
heldInsertionWardRight p = refl

heldCorrelationLeftZero :
  (q : Tangent.ShiftFinitePerturbation) →
  finiteTwoPointCorrelation Tangent.zeroPerturbation q ≡ zero
heldCorrelationLeftZero Tangent.startPerturbation = refl
heldCorrelationLeftZero Tangent.nextPerturbation = refl
heldCorrelationLeftZero Tangent.zeroPerturbation = refl

heldCorrelationRightZero :
  (p : Tangent.ShiftFinitePerturbation) →
  finiteTwoPointCorrelation p Tangent.zeroPerturbation ≡ zero
heldCorrelationRightZero Tangent.startPerturbation = refl
heldCorrelationRightZero Tangent.nextPerturbation = refl
heldCorrelationRightZero Tangent.zeroPerturbation = refl

record ShiftFiniteScalingFusionWard : Setω where
  field
    tangentSemigroup : Tangent.ShiftFiniteTangentSemigroup

    scalingDimension : Tangent.ShiftFinitePerturbation → Nat
    spectrum : List Nat
    startDimension : scalingDimension Tangent.startPerturbation ≡ suc (suc zero)
    nextDimension : scalingDimension Tangent.nextPerturbation ≡ suc zero
    zeroDimension : scalingDimension Tangent.zeroPerturbation ≡ zero

    fusion :
      Tangent.ShiftFinitePerturbation →
      Tangent.ShiftFinitePerturbation →
      Tangent.ShiftFinitePerturbation
    fusion-left-unit :
      (p : Tangent.ShiftFinitePerturbation) →
      fusion Tangent.zeroPerturbation p ≡ p
    fusion-right-unit :
      (p : Tangent.ShiftFinitePerturbation) →
      fusion p Tangent.zeroPerturbation ≡ p
    fusion-associative :
      (p q r : Tangent.ShiftFinitePerturbation) →
      fusion (fusion p q) r ≡ fusion p (fusion q r)

    correlation :
      Tangent.ShiftFinitePerturbation →
      Tangent.ShiftFinitePerturbation →
      Nat
    heldWardLeft :
      (q : Tangent.ShiftFinitePerturbation) →
      correlation
        (Tangent.finiteDerivativeStep Tangent.zeroPerturbation)
        q
      ≡ correlation Tangent.zeroPerturbation q
    heldWardRight :
      (p : Tangent.ShiftFinitePerturbation) →
      correlation
        p
        (Tangent.finiteDerivativeStep Tangent.zeroPerturbation)
      ≡ correlation p Tangent.zeroPerturbation

    nonClaimBoundary : List String

open ShiftFiniteScalingFusionWard public

canonicalShiftFiniteScalingFusionWard :
  ShiftFiniteScalingFusionWard
canonicalShiftFiniteScalingFusionWard =
  record
    { tangentSemigroup = Tangent.canonicalShiftFiniteTangentSemigroup
    ; scalingDimension = finiteScalingDimension
    ; spectrum = finiteScalingSpectrum
    ; startDimension = finiteScalingStartIs2
    ; nextDimension = finiteScalingNextIs1
    ; zeroDimension = finiteScalingZeroIs0
    ; fusion = _⊗p_
    ; fusion-left-unit = fusionLeftUnit
    ; fusion-right-unit = fusionRightUnit
    ; fusion-associative = fusionAssociative
    ; correlation = finiteTwoPointCorrelation
    ; heldWardLeft = heldInsertionWardLeft
    ; heldWardRight = heldInsertionWardRight
    ; nonClaimBoundary =
        "ShiftFiniteScalingFusionWard cross-pollinates the existing finite potential, perturbation class, and exact step"
        ∷ "the finite spectrum is the exact 2,1,0 held-potential/collapse-depth spectrum"
        ∷ "fusion is a finite pointed associative table, not a local operator-product expansion"
        ∷ "heldWardLeft and heldWardRight are exact fixed-insertion identities, not conformal Ward identities"
        ∷ "No anomalous dimension, OPE coefficient, locality, crossing symmetry, stress tensor, or conformal algebra is claimed"
        ∷ []
    }
