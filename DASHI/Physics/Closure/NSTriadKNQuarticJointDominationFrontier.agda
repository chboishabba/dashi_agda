module DASHI.Physics.Closure.NSTriadKNQuarticJointDominationFrontier where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: David Darrow; Elizabeth Carlson; David Goluskin.
-- Title: "Quartic Lyapunov functions for global fluid stability".
-- Venue/year: arXiv preprint, 2026.
-- Journal DOI: none recorded on arXiv v1.
-- arXiv/DataCite DOI: 10.48550/arXiv.2606.18232.
-- arXiv: 2606.18232v1.
-- Uses: equations (21)--(25), separation of quadratic, cubic and quartic
-- derivative parts.
-- Relationship: adapts the degree bookkeeping; the cutoff-uniform
-- discriminant margin below is a DASHI-original 3-D research target and is
-- not claimed by the cited 2-D shear-flow paper.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record ScalarQuadraticQuarticDomination {r : Level} :
    Set (lsuc r) where
  field
    Scalar : Set r
    zero one : Scalar
    add multiply : Scalar → Scalar → Scalar
    negate absolute square : Scalar → Scalar
    _≤_ _<_ : Scalar → Scalar → Set r
    Nonnegative : Scalar → Set r

    quadraticQuarticExpression :
      Scalar → Scalar → Scalar → Scalar
    cubicExpression :
      Scalar → Scalar → Scalar

    scalarQuadraticQuarticDominationIffDiscriminant :
      ∀ a b c →
      Nonnegative a →
      Nonnegative b →
      ((λ : Scalar) →
        Nonnegative λ →
        _≤_ (cubicExpression c λ)
          (quadraticQuarticExpression a b λ))
      →
      _≤_ (square c)
        (multiply
          (add one (add one (add one one)))
          (multiply a b))

    discriminantImpliesScalarQuadraticQuarticDomination :
      ∀ a b c →
      Nonnegative a →
      Nonnegative b →
      _≤_ (square c)
        (multiply
          (add one (add one (add one one)))
          (multiply a b))
      →
      (λ : Scalar) →
      Nonnegative λ →
      _≤_ (cubicExpression c λ)
        (quadraticQuarticExpression a b λ)

    strictScalarDominationFromDiscriminantMargin :
      ∀ eta a b c →
      _<_ zero eta →
      _<_ eta one →
      Nonnegative a →
      Nonnegative b →
      _≤_
        (square c)
        (multiply
          (square (add one (negate eta)))
          (multiply
            (add one (add one (add one one)))
            (multiply a b)))
      →
      (λ : Scalar) →
      Nonnegative λ →
      _≤_
        (cubicExpression c λ)
        (multiply
          (add one (negate eta))
          (quadraticQuarticExpression a b λ))

open ScalarQuadraticQuarticDomination public

record CutoffUniformJointDomination
    {c s r : Level}
    (S : ScalarQuadraticQuarticDomination {r}) :
    Set (lsuc (c ⊔ s ⊔ r)) where
  field
    Cutoff : Set c
    State : Set s

    BoundaryState NonZeroState DangerousState :
      Cutoff → State → Set
    NormalisedShape : Cutoff → State → Set

    scaleState : Scalar S → State → State
    amplitude : Cutoff → State → Scalar S
    normalisedShape : Cutoff → State → State

    quadraticReserve cubicContribution quarticReserve :
      Cutoff → State → Scalar S

    quadraticReserveNonnegative : ∀ N state →
      Nonnegative S (quadraticReserve N state)

    quarticReserveNonnegativeOnAdmissibleBoundary : ∀ N state →
      BoundaryState N state →
      Nonnegative S (quarticReserve N state)

    quadraticPartAmplitudeHomogeneous : ∀ N λ state →
      quadraticReserve N (scaleState λ state)
      ≡ multiply S
          (multiply S λ λ)
          (quadraticReserve N state)

    cubicPartAmplitudeHomogeneous : ∀ N λ state →
      cubicContribution N (scaleState λ state)
      ≡ multiply S
          (multiply S (multiply S λ λ) λ)
          (cubicContribution N state)

    quarticPartAmplitudeHomogeneous : ∀ N λ state →
      quarticReserve N (scaleState λ state)
      ≡ multiply S
          (multiply S (multiply S λ λ) (multiply S λ λ))
          (quarticReserve N state)

    boundaryStateNormalisation : ∀ N state →
      BoundaryState N state →
      NonZeroState N state →
      state ≡ scaleState
        (amplitude N state)
        (normalisedShape N state)

    normalisedShapeIsNormalised : ∀ N state →
      BoundaryState N state →
      NonZeroState N state →
      NormalisedShape N (normalisedShape N state)

    eta : Scalar S
    etaPositive : _<_ S (zero S) eta
    etaLessThanOne : _<_ S eta (one S)

    uniformNormalisedShapeDiscriminantMargin : ∀ N shape →
      NormalisedShape N shape →
      BoundaryState N shape →
      _≤_ S
        (square S (cubicContribution N shape))
        (multiply S
          (square S (add S (one S) (negate S eta)))
          (multiply S
            (add S (one S)
              (add S (one S) (add S (one S) (one S))))
            (multiply S
              (quadraticReserve N shape)
              (quarticReserve N shape))))

    jointDominationReducedToNormalisedShapes : ∀ N state →
      BoundaryState N state →
      NonZeroState N state →
      _≤_ S
        (absolute S (cubicContribution N state))
        (multiply S
          (add S (one S) (negate S eta))
          (add S
            (quadraticReserve N state)
            (quarticReserve N state)))

    strictReserveExcludesEqualityStates : ∀ N state →
      BoundaryState N state →
      NonZeroState N state →
      DangerousState N state →
      _<_ S
        (zero S)
        (add S
          (quadraticReserve N state)
          (quarticReserve N state))

    cutoffUniformJointDomination : ∀ N state →
      BoundaryState N state →
      _≤_ S
        (absolute S (cubicContribution N state))
        (add S
          (quadraticReserve N state)
          (quarticReserve N state))

    strictCutoffUniformJointDomination : ∀ N state →
      BoundaryState N state →
      NonZeroState N state →
      DangerousState N state →
      _<_ S
        (absolute S (cubicContribution N state))
        (add S
          (quadraticReserve N state)
          (quarticReserve N state))

    quarticTimeDerivative : Cutoff → State → Scalar S
    strictQuarticLyapunovDescent : ∀ N state →
      BoundaryState N state →
      NonZeroState N state →
      DangerousState N state →
      _<_ S (quarticTimeDerivative N state) (zero S)

open CutoffUniformJointDomination public

record DerivativePartsAmplitudeHomogeneous
    {c s r : Level}
    {S : ScalarQuadraticQuarticDomination {r}}
    (D : CutoffUniformJointDomination {c} {s} S) :
    Set (c ⊔ s ⊔ r) where
  constructor homogeneous-parts
  field
    quadraticHomogeneous : ∀ N λ state →
      quadraticReserve D N (scaleState D λ state)
      ≡ multiply S
          (multiply S λ λ)
          (quadraticReserve D N state)
    cubicHomogeneous : ∀ N λ state →
      cubicContribution D N (scaleState D λ state)
      ≡ multiply S
          (multiply S (multiply S λ λ) λ)
          (cubicContribution D N state)
    quarticHomogeneous : ∀ N λ state →
      quarticReserve D N (scaleState D λ state)
      ≡ multiply S
          (multiply S (multiply S λ λ) (multiply S λ λ))
          (quarticReserve D N state)

derivativePartsAmplitudeHomogeneous :
  ∀ {c s r}
    {S : ScalarQuadraticQuarticDomination {r}}
    (D : CutoffUniformJointDomination {c} {s} S) →
  DerivativePartsAmplitudeHomogeneous D
derivativePartsAmplitudeHomogeneous D =
  homogeneous-parts
    (quadraticPartAmplitudeHomogeneous D)
    (cubicPartAmplitudeHomogeneous D)
    (quarticPartAmplitudeHomogeneous D)

jointDominationAvailableAtEveryBoundaryState :
  ∀ {c s r}
    {S : ScalarQuadraticQuarticDomination {r}}
    (D : CutoffUniformJointDomination {c} {s} S)
    (N : Cutoff D) (state : State D) →
  BoundaryState D N state →
  _≤_ S
    (absolute S (cubicContribution D N state))
    (add S
      (quadraticReserve D N state)
      (quarticReserve D N state))
jointDominationAvailableAtEveryBoundaryState D N state =
  cutoffUniformJointDomination D N state

jointDominationFrontierPreciselyTyped : Bool
jointDominationFrontierPreciselyTyped = true

jointDominationFrontierPreciselyTypedIsTrue :
  jointDominationFrontierPreciselyTyped ≡ true
jointDominationFrontierPreciselyTypedIsTrue = refl

cutoffUniformJointDominationClosed : Bool
cutoffUniformJointDominationClosed = false

cutoffUniformJointDominationClosedIsFalse :
  cutoffUniformJointDominationClosed ≡ false
cutoffUniformJointDominationClosedIsFalse = refl
