module DASHI.Moonshine.C3CoarseFineRatioTypingExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- John H. Conway and Simon P. Norton,
-- "Monstrous Moonshine", Bulletin of the London Mathematical Society
-- 11 (1979), 308--339.
-- DOI: 10.1112/blms/11.3.308.
--
-- DASHI CONTRIBUTION
--
-- Prevent three different quantities from being called one coarse/fine
-- ratio.  The macro-block multiplicity 10/1, the representation-dimension
-- ratio 196830/53, and the coarse share 53/196883 have different types.
-- Augmentation and nonidentity character evaluation are likewise represented
-- as distinct observations of the same balanced C3 character.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.Monster3BC3RepresentationRingEvaluationExact as C3

data RatioKind : Set where
  macroBlockMultiplicityRatio : RatioKind
  regularCopyMultiplicityRatio : RatioKind
  fineToCoarseDimensionRatio : RatioKind
  coarseShareOfWholeRatio : RatioKind
  fineShareOfWholeRatio : RatioKind

record TypedRatio (kind : RatioKind) : Set where
  constructor typedRatio
  field
    numerator : Nat
    denominator : Nat

open TypedRatio public

macroFineBlockCount : Nat
macroFineBlockCount = C3.tenFineBlocks

regularCopiesPerMacroBlock : Nat
regularCopiesPerMacroBlock = C3.ternaryDepthEight

totalRegularCopyCount : Nat
totalRegularCopyCount = C3.regularBlockMultiplicity

coarseResidualDimension : Nat
coarseResidualDimension = C3.residualMultiplicity C3.monster3BCharacter

fineRegularDimension : Nat
fineRegularDimension = 3 * totalRegularCopyCount

wholeRepresentationDimension : Nat
wholeRepresentationDimension =
  coarseResidualDimension + fineRegularDimension

macroBlockRatio : TypedRatio macroBlockMultiplicityRatio
macroBlockRatio = typedRatio macroFineBlockCount 1

regularCopyRatio : TypedRatio regularCopyMultiplicityRatio
regularCopyRatio = typedRatio totalRegularCopyCount 1

fineToCoarseDimension : TypedRatio fineToCoarseDimensionRatio
fineToCoarseDimension =
  typedRatio fineRegularDimension coarseResidualDimension

coarseShareOfWhole : TypedRatio coarseShareOfWholeRatio
coarseShareOfWhole =
  typedRatio coarseResidualDimension wholeRepresentationDimension

fineShareOfWhole : TypedRatio fineShareOfWholeRatio
fineShareOfWhole =
  typedRatio fineRegularDimension wholeRepresentationDimension

macroFineBlockCountIsTen : macroFineBlockCount ≡ 10
macroFineBlockCountIsTen = refl

regularCopiesPerMacroBlockIs6561 : regularCopiesPerMacroBlock ≡ 6561
regularCopiesPerMacroBlockIs6561 = refl

totalRegularCopyCountIs65610 : totalRegularCopyCount ≡ 65610
totalRegularCopyCountIs65610 = refl

coarseResidualDimensionIs53 : coarseResidualDimension ≡ 53
coarseResidualDimensionIs53 = refl

fineRegularDimensionIs196830 : fineRegularDimension ≡ 196830
fineRegularDimensionIs196830 = refl

wholeRepresentationDimensionIs196883 :
  wholeRepresentationDimension ≡ 196883
wholeRepresentationDimensionIs196883 = refl

macroBlockRatioIsTenOverOne :
  numerator macroBlockRatio ≡ 10
  × denominator macroBlockRatio ≡ 1
macroBlockRatioIsTenOverOne = refl , refl

fineToCoarseDimensionIs196830Over53 :
  numerator fineToCoarseDimension ≡ 196830
  × denominator fineToCoarseDimension ≡ 53
fineToCoarseDimensionIs196830Over53 = refl , refl

coarseShareIs53Over196883 :
  numerator coarseShareOfWhole ≡ 53
  × denominator coarseShareOfWhole ≡ 196883
coarseShareIs53Over196883 = refl , refl

fineShareIs196830Over196883 :
  numerator fineShareOfWhole ≡ 196830
  × denominator fineShareOfWhole ≡ 196883
fineShareIs196830Over196883 = refl , refl

------------------------------------------------------------------------
-- Two evaluations of one object.
------------------------------------------------------------------------

data EvaluationKind : Set where
  identityAugmentation : EvaluationKind
  nonidentityCharacterEvaluation : EvaluationKind

record TypedEvaluation (kind : EvaluationKind) : Set where
  constructor typedEvaluation
  field
    value : Nat
    coarseResidual : Nat
    fineContribution : Nat
    reconstructs : value ≡ coarseResidual + fineContribution

open TypedEvaluation public

identityEvaluation : TypedEvaluation identityAugmentation
identityEvaluation =
  typedEvaluation
    wholeRepresentationDimension
    coarseResidualDimension
    fineRegularDimension
    refl

nonidentityEvaluation : TypedEvaluation nonidentityCharacterEvaluation
nonidentityEvaluation =
  typedEvaluation
    coarseResidualDimension
    coarseResidualDimension
    0
    refl

identityEvaluationValueIs196883 : value identityEvaluation ≡ 196883
identityEvaluationValueIs196883 = refl

nonidentityEvaluationValueIs53 : value nonidentityEvaluation ≡ 53
nonidentityEvaluationValueIs53 = refl

nonidentityFineContributionIsZero :
  fineContribution nonidentityEvaluation ≡ 0
nonidentityFineContributionIsZero = refl

record RatioTypingBoundary : Set where
  constructor ratioTypingBoundary
  field
    blockMultiplicityIsDimensionFraction : Bool
    blockMultiplicityIsDimensionFractionIsFalse :
      blockMultiplicityIsDimensionFraction ≡ false

    characterEvaluationIsTenSectorAverage : Bool
    characterEvaluationIsTenSectorAverageIsFalse :
      characterEvaluationIsTenSectorAverage ≡ false

    regularCharacterCancellationDerivesCoefficientTen : Bool
    regularCharacterCancellationDerivesCoefficientTenIsFalse :
      regularCharacterCancellationDerivesCoefficientTen ≡ false

    c3CancellationMechanismIsMonsterSpecific : Bool
    c3CancellationMechanismIsMonsterSpecificIsFalse :
      c3CancellationMechanismIsMonsterSpecific ≡ false

    dimensionAndTraceAreTypedEvaluationsOfOneCharacter : Bool
    dimensionAndTraceAreTypedEvaluationsOfOneCharacterIsTrue :
      dimensionAndTraceAreTypedEvaluationsOfOneCharacter ≡ true

open RatioTypingBoundary public

canonicalRatioTypingBoundary : RatioTypingBoundary
canonicalRatioTypingBoundary =
  ratioTypingBoundary false refl false refl false refl false refl true refl
