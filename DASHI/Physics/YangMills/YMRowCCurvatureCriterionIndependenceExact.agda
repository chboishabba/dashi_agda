module DASHI.Physics.YangMills.YMRowCCurvatureCriterionIndependenceExact where

------------------------------------------------------------------------
-- ROW C: THE TWO CURVATURE CRITERIA ARE LOGICALLY INDEPENDENT
--
-- The compact-group Heat/Doob route uses a Hessian debt floor
--
--     Hess V_t >= - eta(t) g,
--
-- while the covariance-weighted interpolation route uses
--
--     Cdot (Hess V) Cdot - (1/2) Cddot >= ldot Cdot.
--
-- Already in the pointwise scalar reduction neither implies the other.  This
-- prevents one criterion from silently discharging the other in the frozen
-- Row-C completion contract.  It does not prove Row C.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Rational.Base as ℚ
  using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _≤_; _<_; ½)
import Data.Rational.Properties as ℚP
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness)
open import Relation.Binary.PropositionalEquality using (sym; trans; subst; cong; cong₂)

twoℚ : ℚ
twoℚ = 1ℚ + 1ℚ

halfTimesTwo : ½ * twoℚ ≡ 1ℚ
halfTimesTwo = refl

record ScalarCurvatureDatum : Set where
  field
    covDerivative covSecond hessian logDerivative : ℚ
open ScalarCurvatureDatum public

BBDCondition : ScalarCurvatureDatum → Set
BBDCondition d =
  logDerivative d * covDerivative d
    ≤ ((covDerivative d * hessian d) * covDerivative d) - (½ * covSecond d)

HessianDebtFloor : ℚ → ScalarCurvatureDatum → Set
HessianDebtFloor eta d = (- eta) ≤ hessian d

strictlyBelowIsNotAbove : ∀ {p q} → p < q → ¬ (q ≤ p)
strictlyBelowIsNotAbove p<q q≤p = ℚP.<-irrefl refl (ℚP.<-≤-trans p<q q≤p)

conjugateByOne : ∀ h → (1ℚ * h) * 1ℚ ≡ h
conjugateByOne h = trans (ℚP.*-identityʳ (1ℚ * h)) (ℚP.*-identityˡ h)

halfOfDouble : ∀ h → ½ * (h * twoℚ) ≡ h
halfOfDouble h =
  trans (cong (½ *_) (ℚP.*-comm h twoℚ))
    (trans (sym (ℚP.*-assoc ½ twoℚ h))
      (trans (cong (_* h) halfTimesTwo) (ℚP.*-identityˡ h)))

bbdWitness : ℚ → ScalarCurvatureDatum
bbdWitness eta = record
  { covDerivative = 1ℚ
  ; covSecond     = (- (eta + 1ℚ)) * twoℚ
  ; hessian       = - (eta + 1ℚ)
  ; logDerivative = 0ℚ
  }

bbdWitnessSatisfiesBBD : ∀ eta → BBDCondition (bbdWitness eta)
bbdWitnessSatisfiesBBD eta =
  subst₂ _≤_ leftIsZero rightIsZero ℚP.≤-refl
  where
    h : ℚ
    h = - (eta + 1ℚ)

    leftIsZero : 0ℚ * 1ℚ ≡ 0ℚ
    leftIsZero = ℚP.*-zeroˡ 1ℚ

    rightIsZero : ((1ℚ * h) * 1ℚ) - (½ * (h * twoℚ)) ≡ 0ℚ
    rightIsZero =
      trans (cong₂ (λ x y → x - y) (conjugateByOne h) (halfOfDouble h))
        (ℚP.+-inverseʳ h)

    subst₂ : ∀ {A : Set} {x y u v : A} (R : A → A → Set) →
             x ≡ y → u ≡ v → R y v → R x u
    subst₂ R refl refl r = r

bbdWitnessBreaksFloor : ∀ eta → ¬ (HessianDebtFloor eta (bbdWitness eta))
bbdWitnessBreaksFloor eta = strictlyBelowIsNotAbove below
  where
    etaBelow : eta < eta + 1ℚ
    etaBelow =
      subst (_< eta + 1ℚ) (ℚP.+-identityʳ eta)
        (ℚP.+-monoʳ-< eta (toWitness {a? = 0ℚ ℚP.<? 1ℚ} _))

    below : - (eta + 1ℚ) < - eta
    below = ℚP.neg-antimono-< etaBelow

bbdDoesNotImplyHessianFloor :
  ∀ eta →
  Σ ScalarCurvatureDatum
    (λ d → BBDCondition d × ¬ (HessianDebtFloor eta d))
bbdDoesNotImplyHessianFloor eta =
  bbdWitness eta , bbdWitnessSatisfiesBBD eta , bbdWitnessBreaksFloor eta

floorWitness : ScalarCurvatureDatum
floorWitness = record
  { covDerivative = 1ℚ
  ; covSecond     = twoℚ
  ; hessian       = 0ℚ
  ; logDerivative = 0ℚ
  }

floorWitnessMeetsFloor :
  ∀ eta → 0ℚ ≤ eta → HessianDebtFloor eta floorWitness
floorWitnessMeetsFloor eta 0≤eta = ℚP.neg-antimono-≤ 0≤eta

floorWitnessBreaksBBD : ¬ (BBDCondition floorWitness)
floorWitnessBreaksBBD bbd =
  strictlyBelowIsNotAbove (toWitness {a? = (- 1ℚ) ℚP.<? 0ℚ} _)
    (subst₂ _≤_ (ℚP.*-zeroˡ 1ℚ) rightIsMinusOne bbd)
  where
    rightIsMinusOne : ((1ℚ * 0ℚ) * 1ℚ) - (½ * twoℚ) ≡ - 1ℚ
    rightIsMinusOne = refl

    subst₂ : ∀ {A : Set} {x y u v : A} (R : A → A → Set) →
             x ≡ y → u ≡ v → R x u → R y v
    subst₂ R refl refl r = r

hessianFloorDoesNotImplyBBD :
  Σ ScalarCurvatureDatum
    (λ d → (∀ eta → 0ℚ ≤ eta → HessianDebtFloor eta d) × ¬ (BBDCondition d))
hessianFloorDoesNotImplyBBD =
  floorWitness , floorWitnessMeetsFloor , floorWitnessBreaksBBD
