module DASHI.Physics.YangMills.BalabanSU2ReducedAdjointGaugeCovariance where

------------------------------------------------------------------------
-- Gauge covariance of the concrete adjoint functional calculus.
--
-- The core proof is algebraic rather than coordinate-reflective.  For a unit
-- quaternion q, q* q = 1, hence conjugation preserves quaternion products and
-- therefore preserves the commutator.  The Lie-bracket theorem follows through
-- the already proved quaternion representation of the concrete su(2) bracket.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using
  ( cong; cong₂; sym; trans )

open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( Quaternion
  ; SU2Quaternion
  ; oneQ
  ; _+q_
  ; _*q_
  ; conjugateQ
  ; quaternionOneLeft
  ; quaternionMultiplyAssociative
  ; quaternion
  ; su2InverseLeft
  ; _*R_
  ; -R_
  ; oneR
  ; *-identityˡ
  ; normSquaredQ
  ; unitNormSquared
  )
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  ( SU2LieAlgebra
  ; su2Lie
  ; su2LieExt
  ; lieQuaternion
  ; lieFromQuaternion
  ; lieFromQuaternionLieQuaternion
  ; lieAdd
  ; lieScale
  ; su2Adjoint
  ; su2AdjointAdd
  ; su2AdjointScale
  ; lieQuaternionAdjoint
  ; quaternionNegate
  ; quaternionMultiplyAddLeft
  ; quaternionMultiplyAddRight
  ; quaternionMultiplyNegateLeft
  ; quaternionMultiplyNegateRight
  )
open import DASHI.Physics.YangMills.BalabanSU2AdjointInnerProduct using
  ( su2DotAdjointInvariant )
open import DASHI.Physics.YangMills.BalabanSU2LieBracket using
  ( lieBracket
  ; lieBracketQuaternionCommutator
  )
open import DASHI.Physics.YangMills.BalabanSU2AdjointCubicReduction using
  ( fourR
  ; adCubicCoefficient
  )
open import DASHI.Physics.YangMills.BalabanSU2ReducedAdjointCalculus using
  ( reducedAd
  ; applyReducedAdjoint
  )
open import DASHI.Physics.YangMills.BalabanSU2AdjointMatrixDeterminant using
  ( determinantMatrix3
  ; reducedAdjointMatrix
  ; reducedAdjointDeterminant
  )
open import DASHI.Physics.YangMills.BalabanSU2ReducedAdjointDeterminantProduct using
  ( reducedAdjointDeterminantValue )

rightMultiply : Quaternion → Quaternion → Quaternion
rightMultiply right value = value *q right

conjugateBy : SU2Quaternion → Quaternion → Quaternion
conjugateBy u value =
  (quaternion u *q value) *q conjugateQ (quaternion u)

inverseQuaternionLeft :
  ∀ u →
  conjugateQ (quaternion u) *q quaternion u ≡ oneQ
inverseQuaternionLeft u = cong quaternion (su2InverseLeft u)

unitConjugateMiddle :
  ∀ u value →
  conjugateQ (quaternion u) *q
    ((quaternion u *q value) *q conjugateQ (quaternion u))
  ≡ value *q conjugateQ (quaternion u)
unitConjugateMiddle u value =
  trans
    (sym (quaternionMultiplyAssociative
      (conjugateQ (quaternion u))
      (quaternion u *q value)
      (conjugateQ (quaternion u))))
    (trans
      (cong (rightMultiply (conjugateQ (quaternion u)))
        (sym (quaternionMultiplyAssociative
          (conjugateQ (quaternion u))
          (quaternion u)
          value)))
      (trans
        (cong
          (λ head → (head *q value) *q conjugateQ (quaternion u))
          (inverseQuaternionLeft u))
        (cong (rightMultiply (conjugateQ (quaternion u)))
          (quaternionOneLeft value))))

conjugateByProduct :
  ∀ u left right →
  conjugateBy u left *q conjugateBy u right
  ≡ conjugateBy u (left *q right)
conjugateByProduct u left right =
  trans
    (quaternionMultiplyAssociative
      (quaternion u *q left)
      (conjugateQ (quaternion u))
      ((quaternion u *q right) *q conjugateQ (quaternion u)))
    (trans
      (cong ((quaternion u *q left) *q_)
        (unitConjugateMiddle u right))
      (trans
        (sym (quaternionMultiplyAssociative
          (quaternion u *q left)
          right
          (conjugateQ (quaternion u))))
        (cong (rightMultiply (conjugateQ (quaternion u)))
          (quaternionMultiplyAssociative
            (quaternion u) left right))))

conjugateByAdd :
  ∀ u left right →
  conjugateBy u (left +q right)
  ≡ conjugateBy u left +q conjugateBy u right
conjugateByAdd u left right =
  trans
    (cong (rightMultiply (conjugateQ (quaternion u)))
      (quaternionMultiplyAddLeft (quaternion u) left right))
    (quaternionMultiplyAddRight
      (quaternion u *q left)
      (quaternion u *q right)
      (conjugateQ (quaternion u)))

conjugateByNegate :
  ∀ u value →
  conjugateBy u (quaternionNegate value)
  ≡ quaternionNegate (conjugateBy u value)
conjugateByNegate u value =
  trans
    (cong (rightMultiply (conjugateQ (quaternion u)))
      (quaternionMultiplyNegateRight (quaternion u) value))
    (quaternionMultiplyNegateLeft
      (quaternion u *q value)
      (conjugateQ (quaternion u)))

conjugateByCommutator :
  ∀ u left right →
  conjugateBy u
    ((left *q right) +q quaternionNegate (right *q left))
  ≡
  (conjugateBy u left *q conjugateBy u right)
    +q quaternionNegate
      (conjugateBy u right *q conjugateBy u left)
conjugateByCommutator u left right =
  trans
    (conjugateByAdd u
      (left *q right)
      (quaternionNegate (right *q left)))
    (cong₂ _+q_
      (sym (conjugateByProduct u left right))
      (trans
        (conjugateByNegate u (right *q left))
        (cong quaternionNegate
          (sym (conjugateByProduct u right left)))))

lieQuaternionInjective :
  ∀ {left right} →
  lieQuaternion left ≡ lieQuaternion right →
  left ≡ right
lieQuaternionInjective {left} {right} equality =
  trans
    (sym (lieFromQuaternionLieQuaternion left))
    (trans
      (cong lieFromQuaternion equality)
      (lieFromQuaternionLieQuaternion right))

adjointBracketQuaternion :
  ∀ u Y X →
  lieQuaternion (su2Adjoint u (lieBracket Y X))
  ≡ lieQuaternion
      (lieBracket (su2Adjoint u Y) (su2Adjoint u X))
adjointBracketQuaternion u Y X =
  trans
    (lieQuaternionAdjoint u (lieBracket Y X))
    (trans
      (cong (conjugateBy u)
        (lieBracketQuaternionCommutator Y X))
      (trans
        (conjugateByCommutator u
          (lieQuaternion Y)
          (lieQuaternion X))
        (trans
          (cong₂ _+q_
            (cong₂ _*q_
              (sym (lieQuaternionAdjoint u Y))
              (sym (lieQuaternionAdjoint u X)))
            (cong quaternionNegate
              (cong₂ _*q_
                (sym (lieQuaternionAdjoint u X))
                (sym (lieQuaternionAdjoint u Y)))))
          (sym (lieBracketQuaternionCommutator
            (su2Adjoint u Y)
            (su2Adjoint u X))))))

su2AdjointBracketEquivariant :
  ∀ u Y X →
  su2Adjoint u (lieBracket Y X)
    ≡ lieBracket (su2Adjoint u Y) (su2Adjoint u X)
su2AdjointBracketEquivariant u Y X =
  lieQuaternionInjective (adjointBracketQuaternion u Y X)

lieScaleOne :
  ∀ X → lieScale oneR X ≡ X
lieScaleOne (su2Lie x y z) =
  su2LieExt
    (*-identityˡ x)
    (*-identityˡ y)
    (*-identityˡ z)

su2AdjointBracketNormFactor :
  ∀ u Y X →
  lieBracket (su2Adjoint u Y) (su2Adjoint u X)
  ≡
  lieScale
    (normSquaredQ (quaternion u))
    (su2Adjoint u (lieBracket Y X))
su2AdjointBracketNormFactor u Y X =
  trans
    (sym (su2AdjointBracketEquivariant u Y X))
    (trans
      (sym (lieScaleOne (su2Adjoint u (lieBracket Y X))))
      (cong
        (λ scalar → lieScale scalar (su2Adjoint u (lieBracket Y X)))
        (sym (unitNormSquared u))))

su2AdjointAdSquaredEquivariant :
  ∀ u Y X →
  su2Adjoint u (lieBracket Y (lieBracket Y X))
  ≡
  lieBracket
    (su2Adjoint u Y)
    (lieBracket (su2Adjoint u Y) (su2Adjoint u X))
su2AdjointAdSquaredEquivariant u Y X =
  trans
    (su2AdjointBracketEquivariant u Y (lieBracket Y X))
    (cong
      (lieBracket (su2Adjoint u Y))
      (su2AdjointBracketEquivariant u Y X))

applyReducedAdjointGaugeCovariant :
  ∀ u Y operator X →
  su2Adjoint u (applyReducedAdjoint Y operator X)
  ≡
  applyReducedAdjoint
    (su2Adjoint u Y)
    operator
    (su2Adjoint u X)
applyReducedAdjointGaugeCovariant
  u Y (reducedAd a b c) X =
  trans
    (su2AdjointAdd u
      (lieScale a X)
      (lieAdd
        (lieScale b (lieBracket Y X))
        (lieScale c (lieBracket Y (lieBracket Y X)))))
    (cong₂ lieAdd
      (su2AdjointScale u a X)
      (trans
        (su2AdjointAdd u
          (lieScale b (lieBracket Y X))
          (lieScale c (lieBracket Y (lieBracket Y X))))
        (cong₂ lieAdd
          (trans
            (su2AdjointScale u b (lieBracket Y X))
            (cong (lieScale b)
              (su2AdjointBracketEquivariant u Y X)))
          (trans
            (su2AdjointScale u c
              (lieBracket Y (lieBracket Y X)))
            (cong (lieScale c)
              (su2AdjointAdSquaredEquivariant u Y X))))))

adCubicCoefficientGaugeInvariant :
  ∀ u Y →
  adCubicCoefficient (su2Adjoint u Y)
    ≡ adCubicCoefficient Y
adCubicCoefficientGaugeInvariant u Y =
  cong
    (λ norm → -R (fourR *R norm))
    (su2DotAdjointInvariant u Y Y)

reducedAdjointDeterminantGaugeInvariant :
  ∀ u Y operator →
  reducedAdjointDeterminantValue
    (su2Adjoint u Y) operator
  ≡ reducedAdjointDeterminantValue Y operator
reducedAdjointDeterminantGaugeInvariant
  u Y (reducedAd a b c)
  rewrite adCubicCoefficientGaugeInvariant u Y = refl

reducedAdjointMatrixDeterminantGaugeInvariant :
  ∀ u Y operator →
  determinantMatrix3
    (reducedAdjointMatrix (su2Adjoint u Y) operator)
  ≡
  determinantMatrix3
    (reducedAdjointMatrix Y operator)
reducedAdjointMatrixDeterminantGaugeInvariant
  u Y (reducedAd a b c) =
  trans
    (reducedAdjointDeterminant (su2Adjoint u Y) a b c)
    (trans
      (reducedAdjointDeterminantGaugeInvariant
        u Y (reducedAd a b c))
      (sym (reducedAdjointDeterminant Y a b c)))
