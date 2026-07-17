module DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier where

------------------------------------------------------------------------
-- Concrete SU(2) carrier as the group of unit quaternions over DASHI's
-- canonical real-number authority boundary.
--
-- The quaternion operations are explicit polynomial expressions. Their laws
-- are reduced componentwise and discharged by the standard-library ring
-- solver from one honest foundational socket: the postulated real carrier is
-- a commutative ring. No Yang--Mills source theorem or analytic estimate is
-- assumed here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Structures using (IsCommutativeRing)
open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (nothing)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import Tactic.RingSolver as Solver
import Tactic.RingSolver.Core.AlmostCommutativeRing as ACR

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; 0ℝ
  ; 1ℝ
  ; _+ℝ_
  ; _*ℝ_
  ; -ℝ_
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

derivedRealSolverRing : ACR.AlmostCommutativeRing 0ℓ 0ℓ
derivedRealSolverRing =
  ACR.fromCommutativeRing realCommutativeRing (λ _ → nothing)

realSolverRing : ACR.AlmostCommutativeRing 0ℓ 0ℓ
realSolverRing = record
  { Carrier = ℝ
  ; _≈_ = _≡_
  ; _+_ = _+ℝ_
  ; _*_ = _*ℝ_
  ; -_ = -ℝ_
  ; 0# = 0ℝ
  ; 0≟_ = λ _ → nothing
  ; 1# = 1ℝ
  ; isAlmostCommutativeRing =
      ACR.AlmostCommutativeRing.isAlmostCommutativeRing
        derivedRealSolverRing
  }

module R = ACR.AlmostCommutativeRing realSolverRing
open R using ()
  renaming
    ( _+_ to _+R_
    ; _*_ to _*R_
    ; -_  to -R_
    ; 0#  to zeroR
    ; 1#  to oneR
    )

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
zeroQ = quat zeroR zeroR zeroR zeroR

oneQ : Quaternion
oneQ = quat oneR zeroR zeroR zeroR

_+q_ : Quaternion → Quaternion → Quaternion
quat a0 a1 a2 a3 +q quat b0 b1 b2 b3 =
  quat
    (a0 +R b0)
    (a1 +R b1)
    (a2 +R b2)
    (a3 +R b3)

negQ : Quaternion → Quaternion
negQ (quat a0 a1 a2 a3) =
  quat (-R a0) (-R a1) (-R a2) (-R a3)

conjugateQ : Quaternion → Quaternion
conjugateQ (quat a0 a1 a2 a3) =
  quat a0 (-R a1) (-R a2) (-R a3)

_*q_ : Quaternion → Quaternion → Quaternion
quat a0 a1 a2 a3 *q quat b0 b1 b2 b3 =
  quat
    (((a0 *R b0) +R (-R (a1 *R b1)))
      +R (-R (a2 *R b2))
      +R (-R (a3 *R b3)))
    (((a0 *R b1) +R (a1 *R b0))
      +R (a2 *R b3)
      +R (-R (a3 *R b2)))
    (((a0 *R b2) +R (-R (a1 *R b3)))
      +R (a2 *R b0)
      +R (a3 *R b1))
    (((a0 *R b3) +R (a1 *R b2))
      +R (-R (a2 *R b1))
      +R (a3 *R b0))

normSquaredQ : Quaternion → ℝ
normSquaredQ (quat a0 a1 a2 a3) =
  (((a0 *R a0) +R (a1 *R a1))
    +R (a2 *R a2)
    +R (a3 *R a3))

scaleRealQ : ℝ → Quaternion → Quaternion
scaleRealQ scalar (quat a0 a1 a2 a3) =
  quat
    (scalar *R a0)
    (scalar *R a1)
    (scalar *R a2)
    (scalar *R a3)

quaternionExt :
  ∀ {a b : Quaternion} →
  q0 a ≡ q0 b →
  q1 a ≡ q1 b →
  q2 a ≡ q2 b →
  q3 a ≡ q3 b →
  a ≡ b
quaternionExt {quat a0 a1 a2 a3} {quat .a0 .a1 .a2 .a3}
  refl refl refl refl = refl

------------------------------------------------------------------------
-- Definitional component exposure
------------------------------------------------------------------------

q0Multiply :
  ∀ a b →
  q0 (a *q b)
    ≡
  (((q0 a *R q0 b) +R (-R (q1 a *R q1 b)))
    +R (-R (q2 a *R q2 b))
    +R (-R (q3 a *R q3 b)))
q0Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3) = refl

q1Multiply :
  ∀ a b →
  q1 (a *q b)
    ≡
  (((q0 a *R q1 b) +R (q1 a *R q0 b))
    +R (q2 a *R q3 b)
    +R (-R (q3 a *R q2 b)))
q1Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3) = refl

q2Multiply :
  ∀ a b →
  q2 (a *q b)
    ≡
  (((q0 a *R q2 b) +R (-R (q1 a *R q3 b)))
    +R (q2 a *R q0 b)
    +R (q3 a *R q1 b))
q2Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3) = refl

q3Multiply :
  ∀ a b →
  q3 (a *q b)
    ≡
  (((q0 a *R q3 b) +R (q1 a *R q2 b))
    +R (-R (q2 a *R q1 b))
    +R (q3 a *R q0 b))
q3Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3) = refl

q0Conjugate : ∀ a → q0 (conjugateQ a) ≡ q0 a
q0Conjugate (quat a0 a1 a2 a3) = refl

q1Conjugate : ∀ a → q1 (conjugateQ a) ≡ -R q1 a
q1Conjugate (quat a0 a1 a2 a3) = refl

q2Conjugate : ∀ a → q2 (conjugateQ a) ≡ -R q2 a
q2Conjugate (quat a0 a1 a2 a3) = refl

q3Conjugate : ∀ a → q3 (conjugateQ a) ≡ -R q3 a
q3Conjugate (quat a0 a1 a2 a3) = refl

q0Scale : ∀ scalar a → q0 (scaleRealQ scalar a) ≡ scalar *R q0 a
q0Scale scalar (quat a0 a1 a2 a3) = refl

q1Scale : ∀ scalar a → q1 (scaleRealQ scalar a) ≡ scalar *R q1 a
q1Scale scalar (quat a0 a1 a2 a3) = refl

q2Scale : ∀ scalar a → q2 (scaleRealQ scalar a) ≡ scalar *R q2 a
q2Scale scalar (quat a0 a1 a2 a3) = refl

q3Scale : ∀ scalar a → q3 (scaleRealQ scalar a) ≡ scalar *R q3 a
q3Scale scalar (quat a0 a1 a2 a3) = refl

normSquaredExpand :
  ∀ a →
  normSquaredQ a
    ≡
  (((q0 a *R q0 a) +R (q1 a *R q1 a))
    +R (q2 a *R q2 a)
    +R (q3 a *R q3 a))
normSquaredExpand (quat a0 a1 a2 a3) = refl

------------------------------------------------------------------------
-- Polynomial quaternion laws
------------------------------------------------------------------------

assoc0 : ∀ a b c → q0 ((a *q b) *q c) ≡ q0 (a *q (b *q c))
assoc0 a@(quat a0 a1 a2 a3)
       b@(quat b0 b1 b2 b3)
       c@(quat c0 c1 c2 c3)
  rewrite q0Multiply (a *q b) c
        | q0Multiply a (b *q c)
        | q0Multiply a b | q1Multiply a b | q2Multiply a b | q3Multiply a b
        | q0Multiply b c | q1Multiply b c | q2Multiply b c | q3Multiply b c =
  Solver.solve
    (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
     c0 ∷ c1 ∷ c2 ∷ c3 ∷ [])
    realSolverRing

assoc1 : ∀ a b c → q1 ((a *q b) *q c) ≡ q1 (a *q (b *q c))
assoc1 a@(quat a0 a1 a2 a3)
       b@(quat b0 b1 b2 b3)
       c@(quat c0 c1 c2 c3)
  rewrite q1Multiply (a *q b) c
        | q1Multiply a (b *q c)
        | q0Multiply a b | q1Multiply a b | q2Multiply a b | q3Multiply a b
        | q0Multiply b c | q1Multiply b c | q2Multiply b c | q3Multiply b c =
  Solver.solve
    (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
     c0 ∷ c1 ∷ c2 ∷ c3 ∷ [])
    realSolverRing

assoc2 : ∀ a b c → q2 ((a *q b) *q c) ≡ q2 (a *q (b *q c))
assoc2 a@(quat a0 a1 a2 a3)
       b@(quat b0 b1 b2 b3)
       c@(quat c0 c1 c2 c3)
  rewrite q2Multiply (a *q b) c
        | q2Multiply a (b *q c)
        | q0Multiply a b | q1Multiply a b | q2Multiply a b | q3Multiply a b
        | q0Multiply b c | q1Multiply b c | q2Multiply b c | q3Multiply b c =
  Solver.solve
    (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
     c0 ∷ c1 ∷ c2 ∷ c3 ∷ [])
    realSolverRing

assoc3 : ∀ a b c → q3 ((a *q b) *q c) ≡ q3 (a *q (b *q c))
assoc3 a@(quat a0 a1 a2 a3)
       b@(quat b0 b1 b2 b3)
       c@(quat c0 c1 c2 c3)
  rewrite q3Multiply (a *q b) c
        | q3Multiply a (b *q c)
        | q0Multiply a b | q1Multiply a b | q2Multiply a b | q3Multiply a b
        | q0Multiply b c | q1Multiply b c | q2Multiply b c | q3Multiply b c =
  Solver.solve
    (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
     c0 ∷ c1 ∷ c2 ∷ c3 ∷ [])
    realSolverRing

quaternionMultiplyAssociative :
  ∀ a b c → (a *q b) *q c ≡ a *q (b *q c)
quaternionMultiplyAssociative a b c =
  quaternionExt (assoc0 a b c) (assoc1 a b c) (assoc2 a b c) (assoc3 a b c)

oneLeft0 : ∀ a → q0 (oneQ *q a) ≡ q0 a
oneLeft0 a@(quat a0 a1 a2 a3)
  rewrite q0Multiply oneQ a =
  Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing

oneLeft1 : ∀ a → q1 (oneQ *q a) ≡ q1 a
oneLeft1 a@(quat a0 a1 a2 a3)
  rewrite q1Multiply oneQ a =
  Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing

oneLeft2 : ∀ a → q2 (oneQ *q a) ≡ q2 a
oneLeft2 a@(quat a0 a1 a2 a3)
  rewrite q2Multiply oneQ a =
  Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing

oneLeft3 : ∀ a → q3 (oneQ *q a) ≡ q3 a
oneLeft3 a@(quat a0 a1 a2 a3)
  rewrite q3Multiply oneQ a =
  Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing

quaternionOneLeft : ∀ a → oneQ *q a ≡ a
quaternionOneLeft a =
  quaternionExt (oneLeft0 a) (oneLeft1 a) (oneLeft2 a) (oneLeft3 a)

oneRight0 : ∀ a → q0 (a *q oneQ) ≡ q0 a
oneRight0 a@(quat a0 a1 a2 a3)
  rewrite q0Multiply a oneQ =
  Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing

oneRight1 : ∀ a → q1 (a *q oneQ) ≡ q1 a
oneRight1 a@(quat a0 a1 a2 a3)
  rewrite q1Multiply a oneQ =
  Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing

oneRight2 : ∀ a → q2 (a *q oneQ) ≡ q2 a
oneRight2 a@(quat a0 a1 a2 a3)
  rewrite q2Multiply a oneQ =
  Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing

oneRight3 : ∀ a → q3 (a *q oneQ) ≡ q3 a
oneRight3 a@(quat a0 a1 a2 a3)
  rewrite q3Multiply a oneQ =
  Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing

quaternionOneRight : ∀ a → a *q oneQ ≡ a
quaternionOneRight a =
  quaternionExt (oneRight0 a) (oneRight1 a) (oneRight2 a) (oneRight3 a)

conjugateInvolutive0 : ∀ a → q0 (conjugateQ (conjugateQ a)) ≡ q0 a
conjugateInvolutive0 a rewrite q0Conjugate (conjugateQ a) | q0Conjugate a = refl

conjugateInvolutive1 : ∀ a → q1 (conjugateQ (conjugateQ a)) ≡ q1 a
conjugateInvolutive1 a@(quat a0 a1 a2 a3)
  rewrite q1Conjugate (conjugateQ a) | q1Conjugate a =
  Solver.solve (a1 ∷ []) realSolverRing

conjugateInvolutive2 : ∀ a → q2 (conjugateQ (conjugateQ a)) ≡ q2 a
conjugateInvolutive2 a@(quat a0 a1 a2 a3)
  rewrite q2Conjugate (conjugateQ a) | q2Conjugate a =
  Solver.solve (a2 ∷ []) realSolverRing

conjugateInvolutive3 : ∀ a → q3 (conjugateQ (conjugateQ a)) ≡ q3 a
conjugateInvolutive3 a@(quat a0 a1 a2 a3)
  rewrite q3Conjugate (conjugateQ a) | q3Conjugate a =
  Solver.solve (a3 ∷ []) realSolverRing

quaternionConjugateInvolutive : ∀ a → conjugateQ (conjugateQ a) ≡ a
quaternionConjugateInvolutive a =
  quaternionExt
    (conjugateInvolutive0 a)
    (conjugateInvolutive1 a)
    (conjugateInvolutive2 a)
    (conjugateInvolutive3 a)

quaternionNormConjugate : ∀ a → normSquaredQ (conjugateQ a) ≡ normSquaredQ a
quaternionNormConjugate a@(quat a0 a1 a2 a3)
  rewrite normSquaredExpand (conjugateQ a)
        | q0Conjugate a | q1Conjugate a | q2Conjugate a | q3Conjugate a
        | normSquaredExpand a =
  Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing

quaternionNormMultiplicative :
  ∀ a b → normSquaredQ (a *q b) ≡ normSquaredQ a *R normSquaredQ b
quaternionNormMultiplicative
  a@(quat a0 a1 a2 a3) b@(quat b0 b1 b2 b3)
  rewrite normSquaredExpand (a *q b)
        | q0Multiply a b | q1Multiply a b | q2Multiply a b | q3Multiply a b
        | normSquaredExpand a | normSquaredExpand b =
  Solver.solve
    (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷ [])
    realSolverRing

multiplyConjugateRight0 :
  ∀ a → q0 (a *q conjugateQ a) ≡ q0 (scaleRealQ (normSquaredQ a) oneQ)
multiplyConjugateRight0 a@(quat a0 a1 a2 a3)
  rewrite q0Multiply a (conjugateQ a)
        | q0Conjugate a | q1Conjugate a | q2Conjugate a | q3Conjugate a
        | q0Scale (normSquaredQ a) oneQ | normSquaredExpand a =
  Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing

multiplyConjugateRight1 :
  ∀ a → q1 (a *q conjugateQ a) ≡ q1 (scaleRealQ (normSquaredQ a) oneQ)
multiplyConjugateRight1 a@(quat a0 a1 a2 a3)
  rewrite q1Multiply a (conjugateQ a)
        | q0Conjugate a | q1Conjugate a | q2Conjugate a | q3Conjugate a
        | q1Scale (normSquaredQ a) oneQ | normSquaredExpand a =
  Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing

multiplyConjugateRight2 :
  ∀ a → q2 (a *q conjugateQ a) ≡ q2 (scaleRealQ (normSquaredQ a) oneQ)
multiplyConjugateRight2 a@(quat a0 a1 a2 a3)
  rewrite q2Multiply a (conjugateQ a)
        | q0Conjugate a | q1Conjugate a | q2Conjugate a | q3Conjugate a
        | q2Scale (normSquaredQ a) oneQ | normSquaredExpand a =
  Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing

multiplyConjugateRight3 :
  ∀ a → q3 (a *q conjugateQ a) ≡ q3 (scaleRealQ (normSquaredQ a) oneQ)
multiplyConjugateRight3 a@(quat a0 a1 a2 a3)
  rewrite q3Multiply a (conjugateQ a)
        | q0Conjugate a | q1Conjugate a | q2Conjugate a | q3Conjugate a
        | q3Scale (normSquaredQ a) oneQ | normSquaredExpand a =
  Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing

quaternionMultiplyConjugateRight :
  ∀ a → a *q conjugateQ a ≡ scaleRealQ (normSquaredQ a) oneQ
quaternionMultiplyConjugateRight a =
  quaternionExt
    (multiplyConjugateRight0 a)
    (multiplyConjugateRight1 a)
    (multiplyConjugateRight2 a)
    (multiplyConjugateRight3 a)

multiplyConjugateLeft0 :
  ∀ a → q0 (conjugateQ a *q a) ≡ q0 (scaleRealQ (normSquaredQ a) oneQ)
multiplyConjugateLeft0 a@(quat a0 a1 a2 a3)
  rewrite q0Multiply (conjugateQ a) a
        | q0Conjugate a | q1Conjugate a | q2Conjugate a | q3Conjugate a
        | q0Scale (normSquaredQ a) oneQ | normSquaredExpand a =
  Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing

multiplyConjugateLeft1 :
  ∀ a → q1 (conjugateQ a *q a) ≡ q1 (scaleRealQ (normSquaredQ a) oneQ)
multiplyConjugateLeft1 a@(quat a0 a1 a2 a3)
  rewrite q1Multiply (conjugateQ a) a
        | q0Conjugate a | q1Conjugate a | q2Conjugate a | q3Conjugate a
        | q1Scale (normSquaredQ a) oneQ | normSquaredExpand a =
  Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing

multiplyConjugateLeft2 :
  ∀ a → q2 (conjugateQ a *q a) ≡ q2 (scaleRealQ (normSquaredQ a) oneQ)
multiplyConjugateLeft2 a@(quat a0 a1 a2 a3)
  rewrite q2Multiply (conjugateQ a) a
        | q0Conjugate a | q1Conjugate a | q2Conjugate a | q3Conjugate a
        | q2Scale (normSquaredQ a) oneQ | normSquaredExpand a =
  Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing

multiplyConjugateLeft3 :
  ∀ a → q3 (conjugateQ a *q a) ≡ q3 (scaleRealQ (normSquaredQ a) oneQ)
multiplyConjugateLeft3 a@(quat a0 a1 a2 a3)
  rewrite q3Multiply (conjugateQ a) a
        | q0Conjugate a | q1Conjugate a | q2Conjugate a | q3Conjugate a
        | q3Scale (normSquaredQ a) oneQ | normSquaredExpand a =
  Solver.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []) realSolverRing

quaternionMultiplyConjugateLeft :
  ∀ a → conjugateQ a *q a ≡ scaleRealQ (normSquaredQ a) oneQ
quaternionMultiplyConjugateLeft a =
  quaternionExt
    (multiplyConjugateLeft0 a)
    (multiplyConjugateLeft1 a)
    (multiplyConjugateLeft2 a)
    (multiplyConjugateLeft3 a)

scaleOneQ : scaleRealQ oneR oneQ ≡ oneQ
scaleOneQ = quaternionExt
  (trans (q0Scale oneR oneQ) (Solver.solve [] realSolverRing))
  (trans (q1Scale oneR oneQ) (Solver.solve [] realSolverRing))
  (trans (q2Scale oneR oneQ) (Solver.solve [] realSolverRing))
  (trans (q3Scale oneR oneQ) (Solver.solve [] realSolverRing))

------------------------------------------------------------------------
-- Unit quaternions and the literal gauge-group instance
------------------------------------------------------------------------

record SU2Quaternion : Set where
  constructor su2q
  field
    quaternion : Quaternion
    .unitNormSquared : normSquaredQ quaternion ≡ oneR

open SU2Quaternion public

su2QuaternionExt :
  ∀ {a b : SU2Quaternion} → quaternion a ≡ quaternion b → a ≡ b
su2QuaternionExt {su2q a aUnit} {su2q .a bUnit} refl = refl

oneQUnitNorm : normSquaredQ oneQ ≡ oneR
oneQUnitNorm
  rewrite normSquaredExpand oneQ =
  Solver.solve [] realSolverRing

su2Identity : SU2Quaternion
su2Identity = su2q oneQ oneQUnitNorm

oneTimesOne : oneR *R oneR ≡ oneR
oneTimesOne = Solver.solve [] realSolverRing

su2Multiply : SU2Quaternion → SU2Quaternion → SU2Quaternion
su2Multiply (su2q a aUnit) (su2q b bUnit) =
  su2q (a *q b)
    (trans
      (quaternionNormMultiplicative a b)
      (trans
        (cong₂ _*R_ aUnit bUnit)
        oneTimesOne))

su2Inverse : SU2Quaternion → SU2Quaternion
su2Inverse (su2q a aUnit) =
  su2q (conjugateQ a)
    (trans (quaternionNormConjugate a) aUnit)

su2MultiplyAssociative :
  ∀ a b c →
  su2Multiply (su2Multiply a b) c ≡ su2Multiply a (su2Multiply b c)
su2MultiplyAssociative a b c =
  su2QuaternionExt
    (quaternionMultiplyAssociative
      (quaternion a) (quaternion b) (quaternion c))

su2IdentityLeft : ∀ a → su2Multiply su2Identity a ≡ a
su2IdentityLeft a =
  su2QuaternionExt (quaternionOneLeft (quaternion a))

su2IdentityRight : ∀ a → su2Multiply a su2Identity ≡ a
su2IdentityRight a =
  su2QuaternionExt (quaternionOneRight (quaternion a))

su2InverseLeft : ∀ a → su2Multiply (su2Inverse a) a ≡ su2Identity
su2InverseLeft (su2q a aUnit) =
  su2QuaternionExt
    (trans
      (quaternionMultiplyConjugateLeft a)
      (trans
        (cong (λ scalar → scaleRealQ scalar oneQ) aUnit)
        scaleOneQ))

su2InverseRight : ∀ a → su2Multiply a (su2Inverse a) ≡ su2Identity
su2InverseRight (su2q a aUnit) =
  su2QuaternionExt
    (trans
      (quaternionMultiplyConjugateRight a)
      (trans
        (cong (λ scalar → scaleRealQ scalar oneQ) aUnit)
        scaleOneQ))

su2InverseInvolutive : ∀ a → su2Inverse (su2Inverse a) ≡ a
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
