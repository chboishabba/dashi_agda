module DASHI.Crypto.MLKEMBaseCaseConditionedResidualExact where

------------------------------------------------------------------------
-- CONDITIONING ONE BASECASE COMPONENT: EXACT RESIDUAL EQUATIONS
--
-- Primary source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- Algorithm 12 uses
--   c0 = a0*s0 + a1*s1*gamma
--   c1 = a0*s1 + a1*s0.
-- With additive noise e0,e1 in a public equation, conditioning s0 lets us
-- subtract its known contribution and leaves
--   c0 - a0*s0 = a1*s1*gamma + e0
--   c1 - a1*s0 = a0*s1 + e1.
--
-- Multiplication is opaque here; only additive commutative-group cancellation
-- is used.  The identities therefore instantiate in the modular quotient ring
-- once its operations provide these laws.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

record AdditiveCommutativeGroupWithMul : Set₁ where
  constructor additiveCommutativeGroupWithMul
  field
    Carrier : Set
    zero : Carrier
    _+R_ : Carrier → Carrier → Carrier
    neg : Carrier → Carrier
    _*R_ : Carrier → Carrier → Carrier
    addAssoc : ∀ x y z → (x +R y) +R z ≡ x +R (y +R z)
    addComm : ∀ x y → x +R y ≡ y +R x
    addZeroLeft : ∀ x → zero +R x ≡ x
    addInverseRight : ∀ x → x +R neg x ≡ zero

open AdditiveCommutativeGroupWithMul public

subR :
  (R : AdditiveCommutativeGroupWithMul) →
  Carrier R → Carrier R → Carrier R
subR R x y = _+R_ R x (neg R y)

cancelRight :
  (R : AdditiveCommutativeGroupWithMul) →
  ∀ x tail → _+R_ R (_+R_ R x tail) (neg R x) ≡ tail
cancelRight R x tail =
  trans (addAssoc R x tail (neg R x))
    (trans
      (cong (λ z → _+R_ R x z) (addComm R tail (neg R x)))
      (trans
        (sym (addAssoc R x (neg R x) tail))
        (trans
          (cong (λ z → _+R_ R z tail) (addInverseRight R x))
          (addZeroLeft R tail))))

cancelFirstWithTail :
  (R : AdditiveCommutativeGroupWithMul) →
  ∀ x y e →
  subR R (_+R_ R (_+R_ R x y) e) x ≡ _+R_ R y e
cancelFirstWithTail R x y e =
  trans
    (cong (λ z → _+R_ R z (neg R x)) (addAssoc R x y e))
    (cancelRight R x (_+R_ R y e))

cancelMiddleWithTail :
  (R : AdditiveCommutativeGroupWithMul) →
  ∀ a x e →
  subR R (_+R_ R (_+R_ R a x) e) x ≡ _+R_ R a e
cancelMiddleWithTail R a x e =
  trans
    (cong
      (λ z → subR R (_+R_ R z e) x)
      (addComm R a x))
    (cancelFirstWithTail R x a e)

------------------------------------------------------------------------
-- FIPS-shaped noisy BaseCase equation.
------------------------------------------------------------------------

record NoisyBaseCase
    (R : AdditiveCommutativeGroupWithMul) : Set where
  constructor noisyBaseCase
  field
    a0 a1 s0 s1 gamma e0 e1 c0 c1 : Carrier R
    c0Equation :
      c0 ≡ _+R_ R
        (_+R_ R (_*R_ R a0 s0) (_*R_ R (_*R_ R a1 s1) gamma))
        e0
    c1Equation :
      c1 ≡ _+R_ R
        (_+R_ R (_*R_ R a0 s1) (_*R_ R a1 s0))
        e1

open NoisyBaseCase public

conditionedResidual0 :
  ∀ {R : AdditiveCommutativeGroupWithMul}
    (eq : NoisyBaseCase R) →
  subR R (c0 eq) (_*R_ R (a0 eq) (s0 eq))
  ≡ _+R_ R (_*R_ R (_*R_ R (a1 eq) (s1 eq)) (gamma eq)) (e0 eq)
conditionedResidual0 {R} eq =
  trans
    (cong (λ c → subR R c (_*R_ R (a0 eq) (s0 eq))) (c0Equation eq))
    (cancelFirstWithTail R
      (_*R_ R (a0 eq) (s0 eq))
      (_*R_ R (_*R_ R (a1 eq) (s1 eq)) (gamma eq))
      (e0 eq))

conditionedResidual1 :
  ∀ {R : AdditiveCommutativeGroupWithMul}
    (eq : NoisyBaseCase R) →
  subR R (c1 eq) (_*R_ R (a1 eq) (s0 eq))
  ≡ _+R_ R (_*R_ R (a0 eq) (s1 eq)) (e1 eq)
conditionedResidual1 {R} eq =
  trans
    (cong (λ c → subR R c (_*R_ R (a1 eq) (s0 eq))) (c1Equation eq))
    (cancelMiddleWithTail R
      (_*R_ R (a0 eq) (s1 eq))
      (_*R_ R (a1 eq) (s0 eq))
      (e1 eq))

------------------------------------------------------------------------
-- Blue-team boundary.
------------------------------------------------------------------------

record ConditionedSearchBoundary : Set where
  constructor conditionedSearchBoundary
  field
    conditioningRemovesKnownContribution : Bool
    conditioningRemovesKnownContributionIsTrue :
      conditioningRemovesKnownContribution ≡ true
    remainingSystemIsNoiseFree : Bool
    remainingSystemIsNoiseFreeIsFalse : remainingSystemIsNoiseFree ≡ false
    conditioningAloneProvesCheapRecovery : Bool
    conditioningAloneProvesCheapRecoveryIsFalse :
      conditioningAloneProvesCheapRecovery ≡ false

open ConditionedSearchBoundary public

canonicalConditionedSearchBoundary : ConditionedSearchBoundary
canonicalConditionedSearchBoundary =
  conditionedSearchBoundary true refl false refl false refl
