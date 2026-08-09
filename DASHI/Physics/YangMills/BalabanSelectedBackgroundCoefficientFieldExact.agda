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
-- The literal background supplies an exact ordered star field F_A.  A frame,
-- its Gram matrix and its two-sided Gram inverse all live over F_A.  A rational
-- specialization is authorized only after every literal constraint and frame
-- entry is exhibited as the image of a rational.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
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

sumOverField : ∀ {Index} →
  (coefficientField : ExactOrderedStarField) →
  List Index → (Index → Scalar coefficientField) →
  Scalar coefficientField
sumOverField coefficientField [] value = zero coefficientField
sumOverField coefficientField (index ∷ indices) value =
  _add_ coefficientField
    (value index)
    (sumOverField coefficientField indices value)

record FiniteFieldCoordinates
    (coefficientField : ExactOrderedStarField)
    (Index : Set) : Set₁ where
  field
    coordinates : List Index
    delta : Index → Index → Scalar coefficientField

open FiniteFieldCoordinates public

record GramInverseOverCoefficientField
    (coefficientField : ExactOrderedStarField)
    (FrameIndex : Set)
    (carrier : FiniteFieldCoordinates coefficientField FrameIndex)
    (gramEntry : FrameIndex → FrameIndex → Scalar coefficientField) : Set₁ where
  field
    inverseGramEntry :
      FrameIndex → FrameIndex → Scalar coefficientField

    leftInverseExact : ∀ left right →
      sumOverField coefficientField
        (coordinates carrier)
        (λ middle →
          _mul_ coefficientField
            (inverseGramEntry left middle)
            (gramEntry middle right))
      ≡ delta carrier left right

    rightInverseExact : ∀ left right →
      sumOverField coefficientField
        (coordinates carrier)
        (λ middle →
          _mul_ coefficientField
            (gramEntry left middle)
            (inverseGramEntry middle right))
      ≡ delta carrier left right

open GramInverseOverCoefficientField public

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

constraintEntriesLiveInCoefficientField :
  ∀ {Background ConstraintIndex StateIndex FrameIndex}
    (fieldData : SelectedBackgroundCoefficientField
      Background ConstraintIndex StateIndex FrameIndex)
    background row coordinate →
  Scalar (coefficientField fieldData)
constraintEntriesLiveInCoefficientField fieldData background row coordinate =
  constraintEntry fieldData background row coordinate

frameEntriesLiveInCoefficientField :
  ∀ {Background ConstraintIndex StateIndex FrameIndex}
    (fieldData : SelectedBackgroundCoefficientField
      Background ConstraintIndex StateIndex FrameIndex)
    background coordinate frameCoordinate →
  Scalar (coefficientField fieldData)
frameEntriesLiveInCoefficientField
    fieldData background coordinate frameCoordinate =
  frameEntry fieldData background coordinate frameCoordinate

record SelectedBackgroundFrameAuthority
    {Background ConstraintIndex StateIndex FrameIndex : Set}
    (fieldData : SelectedBackgroundCoefficientField
      Background ConstraintIndex StateIndex FrameIndex)
    (background : Background) : Set₂ where
  field
    frameCarrier :
      FiniteFieldCoordinates (coefficientField fieldData) FrameIndex

    frameGramEntry :
      FrameIndex → FrameIndex → Scalar (coefficientField fieldData)

    frameGramInverse :
      GramInverseOverCoefficientField
        (coefficientField fieldData)
        FrameIndex frameCarrier frameGramEntry

open SelectedBackgroundFrameAuthority public

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
    (background : Background) : Set₂ where
  field
    coefficientFrameAuthority :
      SelectedBackgroundFrameAuthority fieldData background
    realisation : RationalRealisation fieldData background

open RationalFrameAuthority public

rationalFrameAvailableOnlyFromLiteralEntries :
  ∀ {Background ConstraintIndex StateIndex FrameIndex}
    {fieldData : SelectedBackgroundCoefficientField
      Background ConstraintIndex StateIndex FrameIndex}
    {background} →
  SelectedBackgroundFrameAuthority fieldData background →
  RationalRealisation fieldData background →
  RationalFrameAuthority fieldData background
rationalFrameAvailableOnlyFromLiteralEntries authority realisation = record
  { coefficientFrameAuthority = authority
  ; realisation = realisation }

data CoefficientFieldClaim : Set where
  literalSelectedField rationalSpecialisation : CoefficientFieldClaim

literalFieldIsNotRationalSpecialisation :
  literalSelectedField ≡ rationalSpecialisation → ⊥
literalFieldIsNotRationalSpecialisation ()

selectedBackgroundCoefficientFieldLevel : ProofLevel
selectedBackgroundCoefficientFieldLevel = machineChecked

gramInverseOverCoefficientFieldLevel : ProofLevel
gramInverseOverCoefficientFieldLevel = machineChecked

rationalFrameAuthorityLevel : ProofLevel
rationalFrameAuthorityLevel = machineChecked

selectedBackgroundRationalityProducerLevel : ProofLevel
selectedBackgroundRationalityProducerLevel = conditional
