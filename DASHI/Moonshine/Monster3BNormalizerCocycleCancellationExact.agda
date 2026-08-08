module DASHI.Moonshine.Monster3BNormalizerCocycleCancellationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups",
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- I. M. Isaacs,
-- "Character Theory of Finite Groups",
-- Dover Publications, 1994 reprint of the 1976 edition.
-- ISBN: 978-0-486-68014-9; no DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Formalize the exact algebra needed after Stone--von Neumann recognition.
-- A projective normalizer action on the Heisenberg factor has a C3-valued
-- cocycle.  If the multiplicity factor carries the inverse cocycle and pure
-- tensors cancel opposite phases, the induced tensor action is honest.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- The central phase group C3.
------------------------------------------------------------------------

data Phase3 : Set where
  phaseOne phaseZeta phaseZetaSquared : Phase3

infixl 7 _mulPhase_

_mulPhase_ : Phase3 → Phase3 → Phase3
phaseOne mulPhase right = right
phaseZeta mulPhase phaseOne = phaseZeta
phaseZeta mulPhase phaseZeta = phaseZetaSquared
phaseZeta mulPhase phaseZetaSquared = phaseOne
phaseZetaSquared mulPhase phaseOne = phaseZetaSquared
phaseZetaSquared mulPhase phaseZeta = phaseOne
phaseZetaSquared mulPhase phaseZetaSquared = phaseZeta

inversePhase : Phase3 → Phase3
inversePhase phaseOne = phaseOne
inversePhase phaseZeta = phaseZetaSquared
inversePhase phaseZetaSquared = phaseZeta

phaseLeftInverse :
  (phase : Phase3) → inversePhase phase mulPhase phase ≡ phaseOne
phaseLeftInverse phaseOne = refl
phaseLeftInverse phaseZeta = refl
phaseLeftInverse phaseZetaSquared = refl

phaseRightInverse :
  (phase : Phase3) → phase mulPhase inversePhase phase ≡ phaseOne
phaseRightInverse phaseOne = refl
phaseRightInverse phaseZeta = refl
phaseRightInverse phaseZetaSquared = refl

phaseInverseInvolutive :
  (phase : Phase3) → inversePhase (inversePhase phase) ≡ phase
phaseInverseInvolutive phaseOne = refl
phaseInverseInvolutive phaseZeta = refl
phaseInverseInvolutive phaseZetaSquared = refl

phaseAssociative :
  (a b c : Phase3) →
  (a mulPhase b) mulPhase c ≡ a mulPhase (b mulPhase c)
phaseAssociative phaseOne b c = refl
phaseAssociative phaseZeta phaseOne c = refl
phaseAssociative phaseZeta phaseZeta phaseOne = refl
phaseAssociative phaseZeta phaseZeta phaseZeta = refl
phaseAssociative phaseZeta phaseZeta phaseZetaSquared = refl
phaseAssociative phaseZeta phaseZetaSquared phaseOne = refl
phaseAssociative phaseZeta phaseZetaSquared phaseZeta = refl
phaseAssociative phaseZeta phaseZetaSquared phaseZetaSquared = refl
phaseAssociative phaseZetaSquared phaseOne c = refl
phaseAssociative phaseZetaSquared phaseZeta phaseOne = refl
phaseAssociative phaseZetaSquared phaseZeta phaseZeta = refl
phaseAssociative phaseZetaSquared phaseZeta phaseZetaSquared = refl
phaseAssociative phaseZetaSquared phaseZetaSquared phaseOne = refl
phaseAssociative phaseZetaSquared phaseZetaSquared phaseZeta = refl
phaseAssociative phaseZetaSquared phaseZetaSquared phaseZetaSquared = refl

------------------------------------------------------------------------
-- Generic cocycle-compensated tensor action.
------------------------------------------------------------------------

record CocycleCompensatedTensorAction : Set₁ where
  field
    Normalizer Heisenberg Multiplicity Tensor : Set
    compose : Normalizer → Normalizer → Normalizer
    cocycle : Normalizer → Normalizer → Phase3

    actHeisenberg : Normalizer → Heisenberg → Heisenberg
    actMultiplicity : Normalizer → Multiplicity → Multiplicity
    scaleHeisenberg : Phase3 → Heisenberg → Heisenberg
    scaleMultiplicity : Phase3 → Multiplicity → Multiplicity

    pureTensor : Heisenberg → Multiplicity → Tensor
    actTensor : Normalizer → Tensor → Tensor

    tensorActionOnPure :
      (n : Normalizer) →
      (h : Heisenberg) →
      (s : Multiplicity) →
      actTensor n (pureTensor h s)
      ≡ pureTensor (actHeisenberg n h) (actMultiplicity n s)

    heisenbergProjectiveLaw :
      (n m : Normalizer) →
      (h : Heisenberg) →
      actHeisenberg n (actHeisenberg m h)
      ≡ scaleHeisenberg (cocycle n m)
          (actHeisenberg (compose n m) h)

    multiplicityInverseProjectiveLaw :
      (n m : Normalizer) →
      (s : Multiplicity) →
      actMultiplicity n (actMultiplicity m s)
      ≡ scaleMultiplicity (inversePhase (cocycle n m))
          (actMultiplicity (compose n m) s)

    oppositePhasesCancelOnPureTensor :
      (phase : Phase3) →
      (h : Heisenberg) →
      (s : Multiplicity) →
      pureTensor
        (scaleHeisenberg phase h)
        (scaleMultiplicity (inversePhase phase) s)
      ≡ pureTensor h s

open CocycleCompensatedTensorAction public

compensatedTensorActionIsHonestOnPureTensors :
  (action : CocycleCompensatedTensorAction) →
  (n m : Normalizer action) →
  (h : Heisenberg action) →
  (s : Multiplicity action) →
  actTensor action n
    (actTensor action m (pureTensor action h s))
  ≡ actTensor action (compose action n m) (pureTensor action h s)
compensatedTensorActionIsHonestOnPureTensors action n m h s
  rewrite tensorActionOnPure action m h s
        | tensorActionOnPure action n
            (actHeisenberg action m h)
            (actMultiplicity action m s)
        | heisenbergProjectiveLaw action n m h
        | multiplicityInverseProjectiveLaw action n m s
        | oppositePhasesCancelOnPureTensor action
            (cocycle action n m)
            (actHeisenberg action (compose action n m) h)
            (actMultiplicity action (compose action n m) s)
        | tensorActionOnPure action (compose action n m) h s =
  refl
