module DASHI.Physics.YangMills.BalabanSelectedBackgroundCoefficientFieldExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- DASHI CONTRIBUTION
--
-- Prevent the finite reduced-Hessian proof from silently assuming that the
-- kernel of the selected-background constraint matrix is defined over Q.
-- The literal background supplies an exact ordered star field F_A.  A rational
-- frame is available only after every constraint and frame entry is exhibited
-- as the image of a rational.  Otherwise the generic nonorthogonal-frame
-- algebra must be instantiated over F_A rather than over Q.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record ExactOrderedStarField : Set₁ where
  field
    Scalar : Set
    zero one : Scalar
    _add_ _mul_ : Scalar → Scalar → Scalar
    negate star : Scalar → Scalar
    _le_ : Scalar → Scalar → Set

    addAssociative : ∀ left middle right →
      _add_ (_add_ left middle) right
      ≡ _add_ left (_add_ middle right)
    addCommutative : ∀ left right →
      _add_ left right ≡ _add_ right left
    addZeroRight : ∀ value → _add_ value zero ≡ value
    addInverseRight : ∀ value →
      _add_ value (negate value) ≡ zero

    mulAssociative : ∀ left middle right →
      _mul_ (_mul_ left middle) right
      ≡ _mul_ left (_mul_ middle right)
    mulOneRight : ∀ value → _mul_ value one ≡ value
    leftDistributive : ∀ left middle right →
      _mul_ left (_add_ middle right)
      ≡ _add_ (_mul_ left middle) (_mul_ left right)

    starInvolutive : ∀ value → star (star value) ≡ value
    starAdd : ∀ left right →
      star (_add_ left right) ≡ _add_ (star left) (star right)
    starMulReverse : ∀ left right →
      star (_mul_ left right) ≡ _mul_ (star right) (star left)

open ExactOrderedStarField public

record SelectedBackgroundCoefficientField
    (Background ConstraintIndex StateIndex FrameIndex : Set) : Set₂ where
  field
    coefficientField : ExactOrderedStarField

    constraintEntry :
      Background → ConstraintIndex → StateIndex →
      Scalar coefficientField

    frameEntry :
      Background → StateIndex → FrameIndex →
      Scalar coefficientField

open SelectedBackgroundCoefficientField public

record RationalRealisation
    {Background ConstraintIndex StateIndex FrameIndex : Set}
    (fieldData : SelectedBackgroundCoefficientField
      Background ConstraintIndex StateIndex FrameIndex)
    (background : Background) : Set₁ where
  field
    rationalEmbedding : ℚ → Scalar (coefficientField fieldData)

    constraintRationalRepresentative :
      ConstraintIndex → StateIndex → ℚ
    frameRationalRepresentative :
      StateIndex → FrameIndex → ℚ

    constraintEntriesAreRational : ∀ row coordinate →
      constraintEntry fieldData background row coordinate
      ≡ rationalEmbedding
          (constraintRationalRepresentative row coordinate)

    frameEntriesAreRational : ∀ coordinate frameCoordinate →
      frameEntry fieldData background coordinate frameCoordinate
      ≡ rationalEmbedding
          (frameRationalRepresentative coordinate frameCoordinate)

open RationalRealisation public

record RationalFrameAuthority
    {Background ConstraintIndex StateIndex FrameIndex : Set}
    (fieldData : SelectedBackgroundCoefficientField
      Background ConstraintIndex StateIndex FrameIndex)
    (background : Background) : Set₁ where
  field
    realisation : RationalRealisation fieldData background

open RationalFrameAuthority public

rationalFrameAvailableOnlyFromLiteralEntries :
  ∀ {Background ConstraintIndex StateIndex FrameIndex}
    {fieldData : SelectedBackgroundCoefficientField
      Background ConstraintIndex StateIndex FrameIndex}
    {background} →
  RationalRealisation fieldData background →
  RationalFrameAuthority fieldData background
rationalFrameAvailableOnlyFromLiteralEntries realisation = record
  { realisation = realisation }

data CoefficientFieldClaim : Set where
  literalSelectedField rationalSpecialisation : CoefficientFieldClaim

literalFieldIsNotRationalSpecialisation :
  literalSelectedField ≡ rationalSpecialisation → ⊥
literalFieldIsNotRationalSpecialisation ()

selectedBackgroundCoefficientFieldLevel : ProofLevel
selectedBackgroundCoefficientFieldLevel = machineChecked

rationalFrameAuthorityLevel : ProofLevel
rationalFrameAuthorityLevel = machineChecked

selectedBackgroundRationalityProducerLevel : ProofLevel
selectedBackgroundRationalityProducerLevel = conditional
