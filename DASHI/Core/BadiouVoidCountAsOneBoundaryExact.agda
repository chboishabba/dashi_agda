module DASHI.Core.BadiouVoidCountAsOneBoundaryExact where

------------------------------------------------------------------------
-- BADIOU VOID / COUNT-AS-ONE OPERATOR BOUNDARY
--
-- SOURCE CONTEXT
--
-- Alain Badiou, Being and Event, trans. Oliver Feltham, Continuum, 2005.
-- ISBN 9780826458315.  Original French work: L'etre et l'evenement (1988).
--
-- The source motivates the distinction between the void/multiple and the
-- count-as-one as operation.  DASHI formalises only that operator/state
-- separation.  It does not identify Badiou's void with Lacanian inexistence,
-- Irigarayan classification refusal, balanced-ternary zero, or a zeta zero.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- One is represented as an operation result, not as a primitive ontology.
------------------------------------------------------------------------

data PresentedMultiplicity : Set where
  voidPresentation pluralPresentation : PresentedMultiplicity

data CountedPresentation : Set where
  countedAsOne : CountedPresentation

countAsOne : PresentedMultiplicity → CountedPresentation
countAsOne voidPresentation = countedAsOne
countAsOne pluralPresentation = countedAsOne

voidAndPluralShareCountedSurface :
  countAsOne voidPresentation ≡ countAsOne pluralPresentation
voidAndPluralShareCountedSurface = refl

voidIsNotPluralPresentation : voidPresentation ≡ pluralPresentation → ⊥
voidIsNotPluralPresentation ()

------------------------------------------------------------------------
-- Counted surface cannot reconstruct the presented multiplicity.
------------------------------------------------------------------------

record CountAsOneCollision : Set where
  constructor count-as-one-collision
  field
    firstPresented secondPresented : PresentedMultiplicity
    sameCountedPresentation : countAsOne firstPresented ≡ countAsOne secondPresented
    presentedDifference : firstPresented ≡ secondPresented → ⊥

canonicalCountAsOneCollision : CountAsOneCollision
canonicalCountAsOneCollision =
  count-as-one-collision
    voidPresentation pluralPresentation refl voidIsNotPluralPresentation

record BadiouVoidCountBoundary : Set where
  constructor badiou-void-count-boundary
  field
    oneIsPrimitiveSubstanceInThisFormalisation : Bool
    oneIsPrimitiveSubstanceInThisFormalisationIsFalse :
      oneIsPrimitiveSubstanceInThisFormalisation ≡ false
    countAsOneOutputDeterminesFineMultiplicity : Bool
    countAsOneOutputDeterminesFineMultiplicityIsFalse :
      countAsOneOutputDeterminesFineMultiplicity ≡ false
    badiouVoidIsLacanianZeroByDefinition : Bool
    badiouVoidIsLacanianZeroByDefinitionIsFalse :
      badiouVoidIsLacanianZeroByDefinition ≡ false
    badiouVoidIsIrigarayNeitherByDefinition : Bool
    badiouVoidIsIrigarayNeitherByDefinitionIsFalse :
      badiouVoidIsIrigarayNeitherByDefinition ≡ false
    badiouVoidIsRiemannZetaZero : Bool
    badiouVoidIsRiemannZetaZeroIsFalse : badiouVoidIsRiemannZetaZero ≡ false

canonicalBadiouVoidCountBoundary : BadiouVoidCountBoundary
canonicalBadiouVoidCountBoundary =
  badiou-void-count-boundary
    false refl false refl false refl false refl false refl
