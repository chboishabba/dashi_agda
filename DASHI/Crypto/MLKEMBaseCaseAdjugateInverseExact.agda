module DASHI.Crypto.MLKEMBaseCaseAdjugateInverseExact where

------------------------------------------------------------------------
-- ML-KEM BASECASE: EXPLICIT ADJUGATE / NORM INVERSE
--
-- Primary cryptographic source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard",
-- FIPS 203, 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- FIPS BaseCaseMultiply on one quadratic factor X^2 - gamma is
--
--   (a0,a1) * (x0,x1)
--     = (a0*x0 + gamma*a1*x1,
--        a1*x0 + a0*x1).
--
-- Its matrix is
--
--       [ a0       gamma*a1 ]
--       [ a1       a0       ]
--
-- with norm/determinant
--
--       Delta = a0^2 - gamma*a1^2.
--
-- This file proves, over an arbitrary commutative ring, the exact adjugate
-- identity
--
--   adj(a) (M(a) x) = Delta x.
--
-- Given invDelta * Delta = 1, scaling the adjugate by invDelta therefore gives
-- an explicit left inverse.  This is the algebraic producer consumed by
-- MLKEMNTTLocalLeftInverseZeroReflectionExact; no FIPS-specific nonsquare claim
-- is made here.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Algebra.Bundles using (CommutativeRing)
open import Data.Maybe.Base using (nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong₂)
import Tactic.RingSolver.Core.AlmostCommutativeRing as RingCore
import Tactic.RingSolver.NonReflective as RingSolver

open import DASHI.Crypto.MLKEMNTTLocalLeftInverseZeroReflectionExact using
  ( LeftInverseAtZero
  ; left-inverse-at-zero
  )

module _ {c ℓ : Level} (R : CommutativeRing c ℓ) where

  open CommutativeRing R
    renaming
      ( Carrier to F
      ; _+_ to _⊕_
      ; _*_ to _⊗_
      ; -_ to neg
      ; 0# to 0F
      ; 1# to 1F
      )

  private
    solverRing : RingCore.AlmostCommutativeRing c ℓ
    solverRing = RingCore.fromCommutativeRing R (λ _ → nothing)

    module S = RingSolver solverRing

  Pair : Set c
  Pair = F × F

  zeroPair : Pair
  zeroPair = 0F , 0F

  baseCase : F → Pair → Pair → Pair
  baseCase gamma (a0 , a1) (x0 , x1) =
    ( (a0 ⊗ x0) ⊕ ((gamma ⊗ a1) ⊗ x1)
    , (a1 ⊗ x0) ⊕ (a0 ⊗ x1)
    )

  normDelta : F → Pair → F
  normDelta gamma (a0 , a1) =
    (a0 ⊗ a0) ⊕ neg (gamma ⊗ (a1 ⊗ a1))

  adjugateAction : F → Pair → Pair → Pair
  adjugateAction gamma (a0 , a1) (y0 , y1) =
    ( (a0 ⊗ y0) ⊕ neg ((gamma ⊗ a1) ⊗ y1)
    , neg (a1 ⊗ y0) ⊕ (a0 ⊗ y1)
    )

  scalePair : F → Pair → Pair
  scalePair c0 (x0 , x1) = (c0 ⊗ x0) , (c0 ⊗ x1)

  pairExt : {x y : Pair} → proj₁ x ≡ proj₁ y → proj₂ x ≡ proj₂ y → x ≡ y
  pairExt {x = x0 , x1} {y = .x0 , .x1} refl refl = refl

  adjugateBaseCaseIdentity :
    (gamma : F) (a x : Pair) →
    adjugateAction gamma a (baseCase gamma a x)
    ≡ scalePair (normDelta gamma a) x
  adjugateBaseCaseIdentity gamma (a0 , a1) (x0 , x1) =
    pairExt
      (S.solve 5
        (λ gamma a0 a1 x0 x1 →
          ((a0 S.⊗ ((a0 S.⊗ x0) S.⊕ ((gamma S.⊗ a1) S.⊗ x1)))
            S.⊕
           (S.⊝ ((gamma S.⊗ a1) S.⊗
             ((a1 S.⊗ x0) S.⊕ (a0 S.⊗ x1)))))
          S.⊜
          (((a0 S.⊗ a0) S.⊕ (S.⊝ (gamma S.⊗ (a1 S.⊗ a1)))) S.⊗ x0))
        refl gamma a0 a1 x0 x1)
      (S.solve 5
        (λ gamma a0 a1 x0 x1 →
          ((S.⊝ (a1 S.⊗
             ((a0 S.⊗ x0) S.⊕ ((gamma S.⊗ a1) S.⊗ x1))))
            S.⊕
           (a0 S.⊗ ((a1 S.⊗ x0) S.⊕ (a0 S.⊗ x1))))
          S.⊜
          (((a0 S.⊗ a0) S.⊕ (S.⊝ (gamma S.⊗ (a1 S.⊗ a1)))) S.⊗ x1))
        refl gamma a0 a1 x0 x1)

  scaleAssociativeAtInverse :
    (invDelta delta : F) →
    invDelta ⊗ delta ≡ 1F →
    (x : Pair) →
    scalePair invDelta (scalePair delta x) ≡ x
  scaleAssociativeAtInverse invDelta delta inverseLaw (x0 , x1) =
    pairExt
      (S.solve 4
        (λ invD d x one →
          invD S.⊗ (d S.⊗ x) S.⊜ one S.⊗ x)
        inverseLaw invDelta delta x0 1F)
      (S.solve 4
        (λ invD d x one →
          invD S.⊗ (d S.⊗ x) S.⊜ one S.⊗ x)
        inverseLaw invDelta delta x1 1F)

  inverseBaseCase : F → Pair → F → Pair → Pair
  inverseBaseCase gamma a invDelta y =
    scalePair invDelta (adjugateAction gamma a y)

  inverseBaseCaseLeftInverse :
    (gamma : F) (a : Pair) (invDelta : F) →
    invDelta ⊗ normDelta gamma a ≡ 1F →
    (x : Pair) →
    inverseBaseCase gamma a invDelta (baseCase gamma a x) ≡ x
  inverseBaseCaseLeftInverse gamma a invDelta inverseLaw x
    rewrite adjugateBaseCaseIdentity gamma a x =
      scaleAssociativeAtInverse
        invDelta (normDelta gamma a) inverseLaw x

  inverseBaseCaseZero :
    (gamma : F) (a : Pair) (invDelta : F) →
    inverseBaseCase gamma a invDelta zeroPair ≡ zeroPair
  inverseBaseCaseZero gamma (a0 , a1) invDelta =
    pairExt
      (S.solve 4
        (λ invD a0 a1 gamma →
          invD S.⊗
            ((a0 S.⊗ S.con 0) S.⊕
             (S.⊝ ((gamma S.⊗ a1) S.⊗ S.con 0)))
          S.⊜ S.con 0)
        refl invDelta a0 a1 gamma)
      (S.solve 3
        (λ invD a0 a1 →
          invD S.⊗
            ((S.⊝ (a1 S.⊗ S.con 0)) S.⊕ (a0 S.⊗ S.con 0))
          S.⊜ S.con 0)
        refl invDelta a0 a1)

  baseCaseLeftInverseAtZero :
    (gamma : F) (a : Pair) (invDelta : F) →
    invDelta ⊗ normDelta gamma a ≡ 1F →
    LeftInverseAtZero Pair Pair
  baseCaseLeftInverseAtZero gamma a invDelta inverseLaw =
    left-inverse-at-zero
      zeroPair
      zeroPair
      (baseCase gamma a)
      (inverseBaseCase gamma a invDelta)
      (inverseBaseCaseLeftInverse gamma a invDelta inverseLaw)
      (inverseBaseCaseZero gamma a invDelta)
