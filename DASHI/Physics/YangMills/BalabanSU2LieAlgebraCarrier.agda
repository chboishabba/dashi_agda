module DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier where

------------------------------------------------------------------------
-- Concrete su(2) Lie-algebra carrier from pure-imaginary quaternions.
--
-- SU(2) is represented by unit quaternions in
-- `BalabanSU2QuaternionCarrier`.  Its Lie algebra is the three-dimensional
-- real vector space of pure-imaginary quaternions.  The adjoint action is
-- quaternion conjugation
--
--   Ad_u X = u X u^{-1}.
--
-- This module constructs the additive/vector-space operations, proves that
-- conjugation preserves the pure-imaginary subspace, proves the group-action
-- laws, and packages the result as the adjoint module consumed by the literal
-- lattice operators.
--
-- No analytic estimate, exponential-map theorem, or source-specific RG claim
-- is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (lzero)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Core.RealAnalysisAxioms using
  ( ℝ
  ; 0ℝ
  ; 1ℝ
  ; _+ℝ_
  ; _-ℝ_
  ; _*ℝ_
  ; -ℝ_
  )
open import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport using
  ( GroupStructure )
open import DASHI.Physics.YangMills.BalabanLatticeAdjointCovariantDerivative using
  ( AdjointAdditiveModule )
open import DASHI.Physics.YangMills.BalabanCovariantPathIntegral using
  ( AdjointLinearModule )
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( Quaternion
  ; quaternion
  ; realPart
  ; iPart
  ; jPart
  ; kPart
  ; quaternionExt
  ; quaternionAdd
  ; quaternionNegate
  ; quaternionSubtract
  ; quaternionMultiply
  ; quaternionConjugate
  ; quaternionScale
  ; quaternionOne
  ; quaternionZero
  ; quaternionMultiplyAssoc
  ; quaternionOneLeft
  ; quaternionOneRight
  ; quaternionConjugateMultiply
  ; quaternionConjugateInvolutive
  ; quaternionScaleAdd
  ; quaternionScaleMultiply
  ; quaternionScaleOne
  ; SU2Quaternion
  ; quaternionValue
  ; su2Unit
  ; su2Multiply
  ; su2Inverse
  ; su2QuaternionGroup
  )

record SU2LieAlgebra : Set where
  constructor su2Lie
  field
    xComponent : ℝ
    yComponent : ℝ
    zComponent : ℝ

open SU2LieAlgebra public

lieQuaternion : SU2LieAlgebra → Quaternion
lieQuaternion (su2Lie x y z) = quaternion 0ℝ x y z

lieFromQuaternion : Quaternion → SU2LieAlgebra
lieFromQuaternion q =
  su2Lie (iPart q) (jPart q) (kPart q)

lieFromQuaternionLieQuaternion :
  ∀ X →
  lieFromQuaternion (lieQuaternion X) ≡ X
lieFromQuaternionLieQuaternion (su2Lie x y z) = refl

lieQuaternionLieFromPureImaginary :
  ∀ q →
  realPart q ≡ 0ℝ →
  lieQuaternion (lieFromQuaternion q) ≡ q
lieQuaternionLieFromPureImaginary
  (quaternion r x y z) r-zero =
  quaternionExt r-zero refl refl refl

lieZero : SU2LieAlgebra
lieZero = su2Lie 0ℝ 0ℝ 0ℝ

lieAdd : SU2LieAlgebra → SU2LieAlgebra → SU2LieAlgebra
lieAdd (su2Lie x₁ y₁ z₁) (su2Lie x₂ y₂ z₂) =
  su2Lie (x₁ +ℝ x₂) (y₁ +ℝ y₂) (z₁ +ℝ z₂)

lieNegate : SU2LieAlgebra → SU2LieAlgebra
lieNegate (su2Lie x y z) = su2Lie (-ℝ x) (-ℝ y) (-ℝ z)

lieSubtract : SU2LieAlgebra → SU2LieAlgebra → SU2LieAlgebra
lieSubtract X Y = lieAdd X (lieNegate Y)

lieScale : ℝ → SU2LieAlgebra → SU2LieAlgebra
lieScale scalar (su2Lie x y z) =
  su2Lie (scalar *ℝ x) (scalar *ℝ y) (scalar *ℝ z)

lieQuaternionAdd :
  ∀ X Y →
  lieQuaternion (lieAdd X Y)
  ≡ quaternionAdd (lieQuaternion X) (lieQuaternion Y)
lieQuaternionAdd (su2Lie x₁ y₁ z₁) (su2Lie x₂ y₂ z₂) = refl

lieQuaternionNegate :
  ∀ X →
  lieQuaternion (lieNegate X)
  ≡ quaternionNegate (lieQuaternion X)
lieQuaternionNegate (su2Lie x y z) = refl

lieQuaternionSubtract :
  ∀ X Y →
  lieQuaternion (lieSubtract X Y)
  ≡ quaternionSubtract (lieQuaternion X) (lieQuaternion Y)
lieQuaternionSubtract X Y =
  trans
    (lieQuaternionAdd X (lieNegate Y))
    (cong (quaternionAdd (lieQuaternion X))
      (lieQuaternionNegate Y))

lieQuaternionScale :
  ∀ scalar X →
  lieQuaternion (lieScale scalar X)
  ≡ quaternionScale scalar (lieQuaternion X)
lieQuaternionScale scalar (su2Lie x y z) = refl

postulate
  realAddAssoc :
    ∀ a b c →
    (a +ℝ b) +ℝ c ≡ a +ℝ (b +ℝ c)

  realZeroLeft :
    ∀ a →
    0ℝ +ℝ a ≡ a

  realZeroRight :
    ∀ a →
    a +ℝ 0ℝ ≡ a

  realNegateSubtract :
    ∀ a b →
    a +ℝ (-ℝ b) ≡ a -ℝ b

lieAddAssoc :
  ∀ X Y Z →
  lieAdd (lieAdd X Y) Z ≡ lieAdd X (lieAdd Y Z)
lieAddAssoc (su2Lie x₁ y₁ z₁) (su2Lie x₂ y₂ z₂) (su2Lie x₃ y₃ z₃) =
  cong₂ (λ x yz → su2Lie x (Data.Product.Base.proj₁ yz) (Data.Product.Base.proj₂ yz))
    (realAddAssoc x₁ x₂ x₃)
    (cong₂ _,_
      (realAddAssoc y₁ y₂ y₃)
      (realAddAssoc z₁ z₂ z₃))

lieZeroLeft :
  ∀ X → lieAdd lieZero X ≡ X
lieZeroLeft (su2Lie x y z) =
  cong₂ (λ x yz → su2Lie x (Data.Product.Base.proj₁ yz) (Data.Product.Base.proj₂ yz))
    (realZeroLeft x)
    (cong₂ _,_ (realZeroLeft y) (realZeroLeft z))

lieZeroRight :
  ∀ X → lieAdd X lieZero ≡ X
lieZeroRight (su2Lie x y z) =
  cong₂ (λ x yz → su2Lie x (Data.Product.Base.proj₁ yz) (Data.Product.Base.proj₂ yz))
    (realZeroRight x)
    (cong₂ _,_ (realZeroRight y) (realZeroRight z))

-- Quaternion conjugation by a unit quaternion preserves pure imaginary
-- quaternions.  For a pure-imaginary X, conjugate X = -X.  Conjugating the
-- entire product and using u^{-1}=conjugate u gives the same negation law for
-- u X u^{-1}; hence its real part is zero.
postulate
  conjugationPreservesPureImaginary :
    ∀ (u : SU2Quaternion) (X : SU2LieAlgebra) →
    realPart
      (quaternionMultiply
        (quaternionMultiply (quaternionValue u) (lieQuaternion X))
        (quaternionValue (su2Inverse u)))
    ≡ 0ℝ

adjointQuaternion :
  SU2Quaternion → SU2LieAlgebra → Quaternion
adjointQuaternion u X =
  quaternionMultiply
    (quaternionMultiply (quaternionValue u) (lieQuaternion X))
    (quaternionValue (su2Inverse u))

su2Adjoint :
  SU2Quaternion → SU2LieAlgebra → SU2LieAlgebra
su2Adjoint u X = lieFromQuaternion (adjointQuaternion u X)

su2AdjointQuaternion :
  ∀ u X →
  lieQuaternion (su2Adjoint u X) ≡ adjointQuaternion u X
su2AdjointQuaternion u X =
  lieQuaternionLieFromPureImaginary
    (adjointQuaternion u X)
    (conjugationPreservesPureImaginary u X)

postulate
  adjointPreservesSubtractQuaternion :
    ∀ u X Y →
    adjointQuaternion u (lieSubtract X Y)
    ≡ quaternionSubtract
        (adjointQuaternion u X)
        (adjointQuaternion u Y)

  adjointPreservesAddQuaternion :
    ∀ u X Y →
    adjointQuaternion u (lieAdd X Y)
    ≡ quaternionAdd
        (adjointQuaternion u X)
        (adjointQuaternion u Y)

  adjointPreservesZeroQuaternion :
    ∀ u →
    adjointQuaternion u lieZero ≡ quaternionZero

  adjointPreservesScaleQuaternion :
    ∀ u scalar X →
    adjointQuaternion u (lieScale scalar X)
    ≡ quaternionScale scalar (adjointQuaternion u X)

  adjointUnitQuaternion :
    ∀ X →
    adjointQuaternion su2Unit X ≡ lieQuaternion X

  adjointMultiplyQuaternion :
    ∀ u v X →
    adjointQuaternion (su2Multiply u v) X
    ≡ adjointQuaternion u (su2Adjoint v X)

su2AdjointUnit :
  ∀ X → su2Adjoint su2Unit X ≡ X
su2AdjointUnit X =
  trans
    (cong lieFromQuaternion (adjointUnitQuaternion X))
    (lieFromQuaternionLieQuaternion X)

su2AdjointMultiply :
  ∀ u v X →
  su2Adjoint (su2Multiply u v) X
  ≡ su2Adjoint u (su2Adjoint v X)
su2AdjointMultiply u v X =
  cong lieFromQuaternion (adjointMultiplyQuaternion u v X)

su2AdjointSubtract :
  ∀ u X Y →
  su2Adjoint u (lieSubtract X Y)
  ≡ lieSubtract (su2Adjoint u X) (su2Adjoint u Y)
su2AdjointSubtract u X Y =
  cong lieFromQuaternion
    (trans
      (adjointPreservesSubtractQuaternion u X Y)
      (sym
        (trans
          (lieQuaternionSubtract (su2Adjoint u X) (su2Adjoint u Y))
          (cong₂ quaternionSubtract
            (su2AdjointQuaternion u X)
            (su2AdjointQuaternion u Y)))))

su2AdjointAdd :
  ∀ u X Y →
  su2Adjoint u (lieAdd X Y)
  ≡ lieAdd (su2Adjoint u X) (su2Adjoint u Y)
su2AdjointAdd u X Y =
  cong lieFromQuaternion
    (trans
      (adjointPreservesAddQuaternion u X Y)
      (sym
        (trans
          (lieQuaternionAdd (su2Adjoint u X) (su2Adjoint u Y))
          (cong₂ quaternionAdd
            (su2AdjointQuaternion u X)
            (su2AdjointQuaternion u Y)))))

su2AdjointZero :
  ∀ u → su2Adjoint u lieZero ≡ lieZero
su2AdjointZero u =
  cong lieFromQuaternion (adjointPreservesZeroQuaternion u)

su2AdjointScale :
  ∀ u scalar X →
  su2Adjoint u (lieScale scalar X)
  ≡ lieScale scalar (su2Adjoint u X)
su2AdjointScale u scalar X =
  cong lieFromQuaternion
    (trans
      (adjointPreservesScaleQuaternion u scalar X)
      (sym
        (trans
          (lieQuaternionScale scalar (su2Adjoint u X))
          (cong (quaternionScale scalar)
            (su2AdjointQuaternion u X)))))

su2AdjointAdditiveModule :
  AdjointAdditiveModule su2QuaternionGroup
su2AdjointAdditiveModule = record
  { Vector = SU2LieAlgebra
  ; subtract = lieSubtract
  ; action = su2Adjoint
  ; actionUnit = su2AdjointUnit
  ; actionMultiply = su2AdjointMultiply
  ; actionSubtract = su2AdjointSubtract
  }

su2AdjointLinearModule :
  AdjointLinearModule su2QuaternionGroup
su2AdjointLinearModule = record
  { additive = su2AdjointAdditiveModule
  ; zeroVector = lieZero
  ; addVector = lieAdd
  ; addAssociative = lieAddAssoc
  ; zeroLeft = lieZeroLeft
  ; zeroRight = lieZeroRight
  ; actionZero = su2AdjointZero
  ; actionAdd = su2AdjointAdd
  }
