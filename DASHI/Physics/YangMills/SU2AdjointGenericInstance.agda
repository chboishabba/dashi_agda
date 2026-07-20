module DASHI.Physics.YangMills.SU2AdjointGenericInstance where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import Tactic.RingSolver as Solver

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanRealPolynomialRing using
  (_+R_; _*R_; -R_; zeroR; oneR; realSolverRing)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( Quaternion
  ; quat
  ; q0
  ; _+q_
  ; _*q_
  ; oneQ
  ; conjugateQ
  ; quaternionExt
  ; quaternionOneLeft
  ; quaternionOneRight
  ; quaternionMultiplyAssociative
  ; SU2Quaternion
  ; su2q
  ; quaternion
  ; su2Identity
  ; su2Multiply
  ; su2InverseLeft
  )
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  ( SU2LieAlgebra
  ; su2Lie
  ; lieQuaternion
  ; lieFromQuaternion
  ; lieFromQuaternionLieQuaternion
  ; lieAdd
  ; lieScale
  ; quaternionNegate
  ; quaternionScale
  ; quaternionMultiplyAddLeft
  ; quaternionMultiplyAddRight
  ; quaternionMultiplyNegateLeft
  ; quaternionMultiplyNegateRight
  ; quaternionMultiplyScaleLeft
  ; quaternionMultiplyScaleRight
  ; adjointQuaternion
  ; su2Adjoint
  )
open import DASHI.Physics.YangMills.CompactLieLinearAlgebra
open import DASHI.Physics.YangMills.SU2CompactLieAlgebraInstance
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Quaternion identities needed to expose the generic adjoint action.
------------------------------------------------------------------------

conjugateOneQ : conjugateQ oneQ ≡ oneQ
conjugateOneQ =
  quaternionExt
    (Solver.solve [] realSolverRing)
    (Solver.solve [] realSolverRing)
    (Solver.solve [] realSolverRing)
    (Solver.solve [] realSolverRing)

quaternionConjugateProduct :
  ∀ a b → conjugateQ (a *q b) ≡ conjugateQ b *q conjugateQ a
quaternionConjugateProduct
  (quat a₀ a₁ a₂ a₃)
  (quat b₀ b₁ b₂ b₃) =
  quaternionExt
    (Solver.solve (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ []) realSolverRing)
    (Solver.solve (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ []) realSolverRing)
    (Solver.solve (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ []) realSolverRing)
    (Solver.solve (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ []) realSolverRing)

adjointQ : SU2Quaternion → Quaternion → Quaternion
adjointQ u q =
  (quaternion u *q q) *q conjugateQ (quaternion u)

adjointQIdentity : ∀ q → adjointQ su2Identity q ≡ q
adjointQIdentity q =
  trans
    (cong (λ value → value *q conjugateQ oneQ) (quaternionOneLeft q))
    (trans
      (cong (q *q_) conjugateOneQ)
      (quaternionOneRight q))

adjointQProduct :
  ∀ u v q →
  adjointQ (su2Multiply u v) q ≡ adjointQ u (adjointQ v q)
adjointQProduct u v q =
  let a = quaternion u
      b = quaternion v
  in
  trans
    (cong (λ value → ((a *q b) *q q) *q value)
      (quaternionConjugateProduct a b))
    (trans
      (sym (quaternionMultiplyAssociative
        ((a *q b) *q q) (conjugateQ b) (conjugateQ a)))
      (trans
        (cong (λ value → (value *q conjugateQ b) *q conjugateQ a)
          (quaternionMultiplyAssociative a b q))
        (cong (λ value → value *q conjugateQ a)
          (quaternionMultiplyAssociative a (b *q q) (conjugateQ b)))))

adjointQAdd :
  ∀ u p q →
  adjointQ u (p +q q) ≡ adjointQ u p +q adjointQ u q
adjointQAdd u p q =
  trans
    (cong (λ value → value *q conjugateQ (quaternion u))
      (quaternionMultiplyAddLeft (quaternion u) p q))
    (quaternionMultiplyAddRight
      (quaternion u *q p)
      (quaternion u *q q)
      (conjugateQ (quaternion u)))

adjointQNegate :
  ∀ u q →
  adjointQ u (quaternionNegate q) ≡ quaternionNegate (adjointQ u q)
adjointQNegate u q =
  trans
    (cong (λ value → value *q conjugateQ (quaternion u))
      (quaternionMultiplyNegateRight (quaternion u) q))
    (quaternionMultiplyNegateLeft
      (quaternion u *q q)
      (conjugateQ (quaternion u)))

adjointQScale :
  ∀ scalar u q →
  adjointQ u (quaternionScale scalar q)
  ≡ quaternionScale scalar (adjointQ u q)
adjointQScale scalar u q =
  trans
    (cong (λ value → value *q conjugateQ (quaternion u))
      (quaternionMultiplyScaleRight scalar (quaternion u) q))
    (quaternionMultiplyScaleLeft
      scalar
      (quaternion u *q q)
      (conjugateQ (quaternion u)))

unitInverseLeftQuaternion :
  ∀ u → conjugateQ (quaternion u) *q quaternion u ≡ oneQ
unitInverseLeftQuaternion u =
  cong quaternion (su2InverseLeft u)

adjointQMultiply :
  ∀ u p q →
  adjointQ u (p *q q) ≡ adjointQ u p *q adjointQ u q
adjointQMultiply u p q =
  let a = quaternion u
      ai = conjugateQ a
      ai-a≡one = unitInverseLeftQuaternion u
  in
  sym
    (trans
      (quaternionMultiplyAssociative (a *q p) ai ((a *q q) *q ai))
      (trans
        (cong (λ value → (a *q p) *q value)
          (sym (quaternionMultiplyAssociative ai (a *q q) ai)))
        (trans
          (cong (λ value → (a *q p) *q value)
            (cong (λ value → value *q ai)
              (sym (quaternionMultiplyAssociative ai a q))))
          (trans
            (cong (λ value → (a *q p) *q value)
              (cong (λ value → (value *q q) *q ai) ai-a≡one))
            (trans
              (cong (λ value → (a *q p) *q value)
                (cong (λ value → value *q ai) (quaternionOneLeft q)))
              (trans
                (sym (quaternionMultiplyAssociative (a *q p) q ai))
                (cong (λ value → value *q ai)
                  (quaternionMultiplyAssociative a p q))))))))

quaternionCommutator : Quaternion → Quaternion → Quaternion
quaternionCommutator p q =
  (p *q q) +q quaternionNegate (q *q p)

adjointQCommutator :
  ∀ u p q →
  adjointQ u (quaternionCommutator p q)
  ≡ quaternionCommutator (adjointQ u p) (adjointQ u q)
adjointQCommutator u p q =
  trans
    (adjointQAdd u (p *q q) (quaternionNegate (q *q p)))
    (trans
      (cong₂ _+q_
        (adjointQMultiply u p q)
        (adjointQNegate u (q *q p)))
      (cong (λ value → (adjointQ u p *q adjointQ u q) +q quaternionNegate value)
        (adjointQMultiply u q p)))

------------------------------------------------------------------------
-- The coordinate bracket is exactly the pure-imaginary quaternion commutator.
------------------------------------------------------------------------

lieQuaternionBracket :
  ∀ X Y →
  lieQuaternion (su2Bracket X Y)
  ≡ quaternionCommutator (lieQuaternion X) (lieQuaternion Y)
lieQuaternionBracket
  (su2Lie x y z)
  (su2Lie u v w) =
  quaternionExt
    (Solver.solve (x ∷ y ∷ z ∷ u ∷ v ∷ w ∷ []) realSolverRing)
    (Solver.solve (x ∷ y ∷ z ∷ u ∷ v ∷ w ∷ []) realSolverRing)
    (Solver.solve (x ∷ y ∷ z ∷ u ∷ v ∷ w ∷ []) realSolverRing)
    (Solver.solve (x ∷ y ∷ z ∷ u ∷ v ∷ w ∷ []) realSolverRing)

adjointQuaternionPure :
  ∀ u X → q0 (adjointQuaternion u X) ≡ zeroR
adjointQuaternionPure
  (su2q (quat a b c d) unit)
  (su2Lie x y z) =
  Solver.solve (a ∷ b ∷ c ∷ d ∷ x ∷ y ∷ z ∷ []) realSolverRing

lieQuaternionLieFromPure :
  ∀ q → q0 q ≡ zeroR → lieQuaternion (lieFromQuaternion q) ≡ q
lieQuaternionLieFromPure (quat q₀ q₁ q₂ q₃) q₀≡zero =
  quaternionExt (sym q₀≡zero) refl refl refl

lieQuaternionAdjoint :
  ∀ u X →
  lieQuaternion (su2Adjoint u X) ≡ adjointQ u (lieQuaternion X)
lieQuaternionAdjoint u X =
  lieQuaternionLieFromPure
    (adjointQuaternion u X)
    (adjointQuaternionPure u X)

lieQuaternionInjective :
  ∀ {X Y} → lieQuaternion X ≡ lieQuaternion Y → X ≡ Y
lieQuaternionInjective {X} {Y} equality =
  trans
    (sym (lieFromQuaternionLieQuaternion X))
    (trans
      (cong lieFromQuaternion equality)
      (lieFromQuaternionLieQuaternion Y))

su2AdjointIdentityProof : ∀ X → su2Adjoint su2Identity X ≡ X
su2AdjointIdentityProof X =
  lieQuaternionInjective
    (trans
      (lieQuaternionAdjoint su2Identity X)
      (adjointQIdentity (lieQuaternion X)))

su2AdjointProductProof :
  ∀ u v X →
  su2Adjoint (su2Multiply u v) X ≡ su2Adjoint u (su2Adjoint v X)
su2AdjointProductProof u v X =
  lieQuaternionInjective
    (trans
      (lieQuaternionAdjoint (su2Multiply u v) X)
      (trans
        (adjointQProduct u v (lieQuaternion X))
        (sym
          (trans
            (lieQuaternionAdjoint u (su2Adjoint v X))
            (cong (adjointQ u) (lieQuaternionAdjoint v X))))))

su2AdjointAddProof :
  ∀ u X Y →
  su2Adjoint u (lieAdd X Y)
  ≡ lieAdd (su2Adjoint u X) (su2Adjoint u Y)
su2AdjointAddProof u X Y =
  lieQuaternionInjective
    (trans
      (lieQuaternionAdjoint u (lieAdd X Y))
      (trans
        (cong (adjointQ u)
          (DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier.lieQuaternionAdd X Y))
        (trans
          (adjointQAdd u (lieQuaternion X) (lieQuaternion Y))
          (sym
            (trans
              (DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier.lieQuaternionAdd
                (su2Adjoint u X) (su2Adjoint u Y))
              (cong₂ _+q_
                (lieQuaternionAdjoint u X)
                (lieQuaternionAdjoint u Y)))))))

su2AdjointScaleProof :
  ∀ u scalar X →
  su2Adjoint u (lieScale scalar X)
  ≡ lieScale scalar (su2Adjoint u X)
su2AdjointScaleProof u scalar X =
  lieQuaternionInjective
    (trans
      (lieQuaternionAdjoint u (lieScale scalar X))
      (trans
        (cong (adjointQ u)
          (DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier.lieQuaternionScale scalar X))
        (trans
          (adjointQScale scalar u (lieQuaternion X))
          (sym
            (trans
              (DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier.lieQuaternionScale
                scalar (su2Adjoint u X))
              (cong (quaternionScale scalar) (lieQuaternionAdjoint u X)))))))

su2AdjointBracketProof :
  ∀ u X Y →
  su2Adjoint u (su2Bracket X Y)
  ≡ su2Bracket (su2Adjoint u X) (su2Adjoint u Y)
su2AdjointBracketProof u X Y =
  lieQuaternionInjective
    (trans
      (lieQuaternionAdjoint u (su2Bracket X Y))
      (trans
        (cong (adjointQ u) (lieQuaternionBracket X Y))
        (trans
          (adjointQCommutator u (lieQuaternion X) (lieQuaternion Y))
          (sym
            (trans
              (lieQuaternionBracket (su2Adjoint u X) (su2Adjoint u Y))
              (cong₂ quaternionCommutator
                (lieQuaternionAdjoint u X)
                (lieQuaternionAdjoint u Y)))))))

su2AdjointLinearAction :
  AdjointLinearAction su2GenericGroup su2GenericLieAlgebra su2RealLieAlgebra
su2AdjointLinearAction = record
  { Ad = su2Adjoint
  ; adjointIdentity = su2AdjointIdentityProof
  ; adjointProduct = su2AdjointProductProof
  ; adjointAdd = su2AdjointAddProof
  ; adjointScale = su2AdjointScaleProof
  ; adjointBracket = su2AdjointBracketProof
  }

su2AdjointGenericProofLevel : ProofLevel
su2AdjointGenericProofLevel = machineChecked
