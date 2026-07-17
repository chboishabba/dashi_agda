module DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier where

------------------------------------------------------------------------
-- Concrete SU(2) carrier as the group of unit quaternions over DASHI's
-- canonical real-number authority boundary.
--
-- The quaternion operations are explicit polynomial expressions.  Their
-- algebraic laws are discharged by the standard-library ring solver from one
-- honest foundational socket: the postulated real carrier is a commutative
-- ring.  No Yang--Mills source theorem or analytic estimate is assumed here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Structures using (IsCommutativeRing)
open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (nothing)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import Tactic.RingSolver as Solver
import Tactic.RingSolver.Core.AlmostCommutativeRing as ACR

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; 0ℝ
  ; 1ℝ
  ; _+ℝ_
  ; _*ℝ_
  ; -ℝ_
  ; mulOneʳ
  )
open import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport using
  ( GroupStructure )

------------------------------------------------------------------------
-- Real polynomial solver socket
------------------------------------------------------------------------

postulate
  realIsCommutativeRing :
    IsCommutativeRing _≡_ _+ℝ_ _*ℝ_ -ℝ_ 0ℝ 1ℝ

realCommutativeRing : CommutativeRing 0ℓ 0ℓ
realCommutativeRing = record
  { Carrier = ℝ
  ; _≈_ = _≡_
  ; _+_ = _+ℝ_
  ; _*_ = _*ℝ_
  ; -_ = -ℝ_
  ; 0# = 0ℝ
  ; 1# = 1ℝ
  ; isCommutativeRing = realIsCommutativeRing
  }

realSolverRing : ACR.AlmostCommutativeRing 0ℓ 0ℓ
realSolverRing =
  ACR.fromCommutativeRing realCommutativeRing (λ _ → nothing)

------------------------------------------------------------------------
-- Quaternion algebra
------------------------------------------------------------------------

record Quaternion : Set where
  constructor quat
  field
    q0 q1 q2 q3 : ℝ

open Quaternion public

infixl 30 _*q_
infixl 20 _+q_

zeroQ : Quaternion
zeroQ = quat 0ℝ 0ℝ 0ℝ 0ℝ

oneQ : Quaternion
oneQ = quat 1ℝ 0ℝ 0ℝ 0ℝ

_+q_ : Quaternion → Quaternion → Quaternion
quat a0 a1 a2 a3 +q quat b0 b1 b2 b3 =
  quat
    (a0 +ℝ b0)
    (a1 +ℝ b1)
    (a2 +ℝ b2)
    (a3 +ℝ b3)

negQ : Quaternion → Quaternion
negQ (quat a0 a1 a2 a3) =
  quat (-ℝ a0) (-ℝ a1) (-ℝ a2) (-ℝ a3)

conjugateQ : Quaternion → Quaternion
conjugateQ (quat a0 a1 a2 a3) =
  quat a0 (-ℝ a1) (-ℝ a2) (-ℝ a3)

_*q_ : Quaternion → Quaternion → Quaternion
quat a0 a1 a2 a3 *q quat b0 b1 b2 b3 =
  quat
    (((a0 *ℝ b0) +ℝ (-ℝ (a1 *ℝ b1)))
      +ℝ (-ℝ (a2 *ℝ b2))
      +ℝ (-ℝ (a3 *ℝ b3)))
    (((a0 *ℝ b1) +ℝ (a1 *ℝ b0))
      +ℝ (a2 *ℝ b3)
      +ℝ (-ℝ (a3 *ℝ b2)))
    (((a0 *ℝ b2) +ℝ (-ℝ (a1 *ℝ b3)))
      +ℝ (a2 *ℝ b0)
      +ℝ (a3 *ℝ b1))
    (((a0 *ℝ b3) +ℝ (a1 *ℝ b2))
      +ℝ (-ℝ (a2 *ℝ b1))
      +ℝ (a3 *ℝ b0))

normSquaredQ : Quaternion → ℝ
normSquaredQ (quat a0 a1 a2 a3) =
  (((a0 *ℝ a0) +ℝ (a1 *ℝ a1))
    +ℝ (a2 *ℝ a2)
    +ℝ (a3 *ℝ a3))

scaleRealQ : ℝ → Quaternion → Quaternion
scaleRealQ scalar (quat a0 a1 a2 a3) =
  quat
    (scalar *ℝ a0)
    (scalar *ℝ a1)
    (scalar *ℝ a2)
    (scalar *ℝ a3)

quaternionExt :
  ∀ {a b : Quaternion} →
  q0 a ≡ q0 b →
  q1 a ≡ q1 b →
  q2 a ≡ q2 b →
  q3 a ≡ q3 b →
  a ≡ b
quaternionExt {quat a0 a1 a2 a3} {quat .a0 .a1 .a2 .a3}
  refl refl refl refl = refl

quaternionMultiplyAssociative :
  ∀ a b c →
  (a *q b) *q c ≡ a *q (b *q c)
quaternionMultiplyAssociative
  (quat a0 a1 a2 a3)
  (quat b0 b1 b2 b3)
  (quat c0 c1 c2 c3) =
  quaternionExt
    (Solver.solve
      (a0 ∷ a1 ∷ a2 ∷ a3 ∷
       b0 ∷ b1 ∷ b2 ∷ b3 ∷
       c0 ∷ c1 ∷ c2 ∷ c3 ∷ [])
      realSolverRing)
    (Solver.solve
      (a0 ∷ a1 ∷ a2 ∷ a3 ∷
       b0 ∷ b1 ∷ b2 ∷ b3 ∷
       c0 ∷ c1 ∷ c2 ∷ c3 ∷ [])
      realSolverRing)
    (Solver.solve
      (a0 ∷ a1 ∷ a2 ∷ a3 ∷
       b0 ∷ b1 ∷ b2 ∷ b3 ∷
       c0 ∷ c1 ∷ c2 ∷ c3 ∷ [])
      realSolverRing)
    (Solver.solve
      (a0 ∷ a1 ∷ a2 ∷ a3 ∷
       b0 ∷ b1 ∷ b2 ∷ b3 ∷
       c0 ∷ c1 ∷ c2 ∷ c3 ∷ [])
      realSolverRing)

quaternionOneLeft :
  ∀ a → oneQ *q a ≡ a
quaternionOneLeft (quat a0 a1 a2 a3) =
  quaternionExt
    (Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing)
    (Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing)
    (Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing)
    (Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing)

quaternionOneRight :
  ∀ a → a *q oneQ ≡ a
quaternionOneRight (quat a0 a1 a2 a3) =
  quaternionExt
    (Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing)
    (Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing)
    (Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing)
    (Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing)

quaternionConjugateInvolutive :
  ∀ a → conjugateQ (conjugateQ a) ≡ a
quaternionConjugateInvolutive (quat a0 a1 a2 a3) =
  quaternionExt
    refl
    (Solver.solve (a1 ∷ []) realSolverRing)
    (Solver.solve (a2 ∷ []) realSolverRing)
    (Solver.solve (a3 ∷ []) realSolverRing)

quaternionNormConjugate :
  ∀ a → normSquaredQ (conjugateQ a) ≡ normSquaredQ a
quaternionNormConjugate (quat a0 a1 a2 a3) =
  Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing

quaternionNormMultiplicative :
  ∀ a b →
  normSquaredQ (a *q b)
    ≡ normSquaredQ a *ℝ normSquaredQ b
quaternionNormMultiplicative
  (quat a0 a1 a2 a3)
  (quat b0 b1 b2 b3) =
  Solver.solve
    (a0 ∷ a1 ∷ a2 ∷ a3 ∷
     b0 ∷ b1 ∷ b2 ∷ b3 ∷ [])
    realSolverRing

quaternionMultiplyConjugateRight :
  ∀ a →
  a *q conjugateQ a ≡ scaleRealQ (normSquaredQ a) oneQ
quaternionMultiplyConjugateRight (quat a0 a1 a2 a3) =
  quaternionExt
    (Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing)
    (Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing)
    (Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing)
    (Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing)

quaternionMultiplyConjugateLeft :
  ∀ a →
  conjugateQ a *q a ≡ scaleRealQ (normSquaredQ a) oneQ
quaternionMultiplyConjugateLeft (quat a0 a1 a2 a3) =
  quaternionExt
    (Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing)
    (Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing)
    (Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing)
    (Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing)

scaleOneQ :
  scaleRealQ 1ℝ oneQ ≡ oneQ
scaleOneQ = quaternionOneLeft oneQ

------------------------------------------------------------------------
-- Unit quaternions and the literal gauge-group instance
------------------------------------------------------------------------

record SU2Quaternion : Set where
  constructor su2q
  field
    quaternion : Quaternion
    .unitNormSquared : normSquaredQ quaternion ≡ 1ℝ

open SU2Quaternion public

su2QuaternionExt :
  ∀ {a b : SU2Quaternion} →
  quaternion a ≡ quaternion b →
  a ≡ b
su2QuaternionExt {su2q a aUnit} {su2q .a bUnit} refl = refl

su2Identity : SU2Quaternion
su2Identity = su2q oneQ
  (Solver.solve ([] {A = ℝ}) realSolverRing)

su2Multiply : SU2Quaternion → SU2Quaternion → SU2Quaternion
su2Multiply (su2q a aUnit) (su2q b bUnit) =
  su2q (a *q b)
    (trans
      (quaternionNormMultiplicative a b)
      (trans
        (cong₂ _*ℝ_ aUnit bUnit)
        (mulOneʳ 1ℝ)))

su2Inverse : SU2Quaternion → SU2Quaternion
su2Inverse (su2q a aUnit) =
  su2q (conjugateQ a)
    (trans (quaternionNormConjugate a) aUnit)

su2MultiplyAssociative :
  ∀ a b c →
  su2Multiply (su2Multiply a b) c
    ≡ su2Multiply a (su2Multiply b c)
su2MultiplyAssociative a b c =
  su2QuaternionExt
    (quaternionMultiplyAssociative
      (quaternion a) (quaternion b) (quaternion c))

su2IdentityLeft :
  ∀ a → su2Multiply su2Identity a ≡ a
su2IdentityLeft a =
  su2QuaternionExt (quaternionOneLeft (quaternion a))

su2IdentityRight :
  ∀ a → su2Multiply a su2Identity ≡ a
su2IdentityRight a =
  su2QuaternionExt (quaternionOneRight (quaternion a))

su2InverseLeft :
  ∀ a → su2Multiply (su2Inverse a) a ≡ su2Identity
su2InverseLeft (su2q a aUnit) =
  su2QuaternionExt
    (trans
      (quaternionMultiplyConjugateLeft a)
      (trans
        (cong (λ scalar → scaleRealQ scalar oneQ) aUnit)
        scaleOneQ))

su2InverseRight :
  ∀ a → su2Multiply a (su2Inverse a) ≡ su2Identity
su2InverseRight (su2q a aUnit) =
  su2QuaternionExt
    (trans
      (quaternionMultiplyConjugateRight a)
      (trans
        (cong (λ scalar → scaleRealQ scalar oneQ) aUnit)
        scaleOneQ))

su2InverseInvolutive :
  ∀ a → su2Inverse (su2Inverse a) ≡ a
su2InverseInvolutive a =
  su2QuaternionExt
    (quaternionConjugateInvolutive (quaternion a))

su2QuaternionGroup : GroupStructure
su2QuaternionGroup = record
  { Carrier = SU2Quaternion
  ; unit = su2Identity
  ; multiply = su2Multiply
  ; inverse = su2Inverse
  ; multiplyAssoc = su2MultiplyAssociative
  ; unitLeft = su2IdentityLeft
  ; unitRight = su2IdentityRight
  ; inverseLeft = su2InverseLeft
  ; inverseRight = su2InverseRight
  ; inverseInvolutive = su2InverseInvolutive
  }
