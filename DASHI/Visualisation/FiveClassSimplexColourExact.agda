module DASHI.Visualisation.FiveClassSimplexColourExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Five nonnegative activities, their scale, and a denominator-ten simplex
-- witness are separate carriers.  The finite weights are exact rationals
-- represented by numerators over one shared denominator.

record Activity5 : Set where
  constructor activity5
  field
    activityA : Nat
    activityB : Nat
    activityC : Nat
    activityD : Nat
    activityE : Nat

open Activity5 public

totalActivity : Activity5 → Nat
totalActivity activity =
  activityA activity
  +
  activityB activity
  +
  activityC activity
  +
  activityD activity
  +
  activityE activity

canonicalActivity : Activity5
canonicalActivity = activity5 1 2 3 2 2

canonicalActivityTotalIsTen :
  totalActivity canonicalActivity ≡ 10
canonicalActivityTotalIsTen = refl

record SimplexWeight5 : Set where
  constructor simplexWeight5
  field
    weightA : Nat
    weightB : Nat
    weightC : Nat
    weightD : Nat
    weightE : Nat
    denominator : Nat

open SimplexWeight5 public

weightNumeratorTotal : SimplexWeight5 → Nat
weightNumeratorTotal weight =
  weightA weight
  +
  weightB weight
  +
  weightC weight
  +
  weightD weight
  +
  weightE weight

canonicalWeight : SimplexWeight5
canonicalWeight = simplexWeight5 1 2 3 2 2 10

canonicalWeightCloses :
  weightNumeratorTotal canonicalWeight ≡ denominator canonicalWeight
canonicalWeightCloses = refl

data Validity : Set where
  invalidPoint : Validity
  validPoint : Validity

record RenderObservation : Set where
  constructor renderObservation
  field
    mixture : SimplexWeight5
    activityScale : Nat
    validity : Validity

open RenderObservation public

canonicalObservation : RenderObservation
canonicalObservation =
  renderObservation canonicalWeight 10 validPoint

validityAndActivityAreIndependent :
  validity canonicalObservation ≡ validPoint
  ×
  activityScale canonicalObservation ≡ 10
validityAndActivityAreIndependent = refl , refl

------------------------------------------------------------------------
-- A finite five-class-to-three-channel colour map.  The explicit collision
-- witnesses the dimensional obstruction: a three-channel display cannot be
-- assumed injective on all five-class mixtures.

data PureClass : Set where
  classA : PureClass
  classB : PureClass
  classC : PureClass
  classD : PureClass
  classE : PureClass

record RGB : Set where
  constructor rgb
  field
    red : Nat
    green : Nat
    blue : Nat

open RGB public

fixedColour : PureClass → RGB
fixedColour classA = rgb 1 0 0
fixedColour classB = rgb 0 1 0
fixedColour classC = rgb 0 0 1
fixedColour classD = rgb 1 1 0
fixedColour classE = rgb 1 1 0

distinctClassesCollide :
  fixedColour classD ≡ fixedColour classE
distinctClassesCollide = refl

classesRemainDistinct : classD ≡ classE → ⊥
classesRemainDistinct ()

------------------------------------------------------------------------
-- A common positive attenuation changes total activity but not the declared
-- relative-composition class.  A class-specific attenuation can change it.

data ActivityProfile : Set where
  baseProfile : ActivityProfile
  commonScaledProfile : ActivityProfile
  classSpecificProfile : ActivityProfile

profileMixture : ActivityProfile → SimplexWeight5
profileMixture baseProfile =
  simplexWeight5 1 2 3 2 2 10
profileMixture commonScaledProfile =
  simplexWeight5 1 2 3 2 2 10
profileMixture classSpecificProfile =
  simplexWeight5 1 1 5 1 2 10

commonMultiplicativePenaltyCancelsFromMixture :
  profileMixture baseProfile
  ≡
  profileMixture commonScaledProfile
commonMultiplicativePenaltyCancelsFromMixture = refl

classSpecificPenaltyCanChangeMixture :
  profileMixture baseProfile
  ≡
  profileMixture classSpecificProfile
  →
  ⊥
classSpecificPenaltyCanChangeMixture ()

data AmbiguityLevel : Set where
  exactTie : AmbiguityLevel
  smallGap : AmbiguityLevel
  largeGap : AmbiguityLevel

nonnegativeAttenuation : AmbiguityLevel → Nat
nonnegativeAttenuation exactTie = 0
nonnegativeAttenuation smallGap = 1
nonnegativeAttenuation largeGap = 2

tieHasStrongestSuppression :
  nonnegativeAttenuation exactTie ≡ 0
tieHasStrongestSuppression = refl

------------------------------------------------------------------------
-- Sign correction for the proposed GELU(-gamma gap) ambiguity factor.  A
-- negative ambiguity value inserted into 1-lambda*tau amplifies instead of
-- suppressing a positive-gap pixel.

data TieFactorEffect : Set where
  suppressesActivity : TieFactorEffect
  leavesActivityUnchanged : TieFactorEffect
  amplifiesActivity : TieFactorEffect

legacySignedTieEffect : AmbiguityLevel → TieFactorEffect
legacySignedTieEffect exactTie = leavesActivityUnchanged
legacySignedTieEffect smallGap = amplifiesActivity
legacySignedTieEffect largeGap = amplifiesActivity

correctedNonnegativeTieEffect : AmbiguityLevel → TieFactorEffect
correctedNonnegativeTieEffect exactTie = suppressesActivity
correctedNonnegativeTieEffect smallGap = suppressesActivity
correctedNonnegativeTieEffect largeGap = leavesActivityUnchanged

legacyPositiveGapAmplifies :
  legacySignedTieEffect smallGap ≡ amplifiesActivity
legacyPositiveGapAmplifies = refl

correctedTieSuppresses :
  correctedNonnegativeTieEffect exactTie ≡ suppressesActivity
correctedTieSuppresses = refl

data ColourBasisMode : Set where
  localPCABasis : ColourBasisMode
  globalPCABasis : ColourBasisMode
  fixedPaletteBasis : ColourBasisMode
  rawChannelPanels : ColourBasisMode

intrinsicSimplexDimension : Nat
intrinsicSimplexDimension = 4

displayChannelDimension : Nat
displayChannelDimension = 3

displayDropsAtLeastOneIntrinsicDirection :
  intrinsicSimplexDimension ≡ suc displayChannelDimension
displayDropsAtLeastOneIntrinsicDirection = refl

record FiveClassSimplexColourBoundary : Set where
  constructor fiveClassSimplexColourBoundary
  field
    rawGELUIsAutomaticallyNonnegativeActivity : Bool
    rawGELUIsAutomaticallyNonnegativeActivityIsFalse :
      rawGELUIsAutomaticallyNonnegativeActivity ≡ false

    fiveClassToRGBIsInjective : Bool
    fiveClassToRGBIsInjectiveIsFalse :
      fiveClassToRGBIsInjective ≡ false

    localPCAMaximisesSemanticColourSeparation : Bool
    localPCAMaximisesSemanticColourSeparationIsFalse :
      localPCAMaximisesSemanticColourSeparation ≡ false

    perSliceMinMaxPreservesCrossSliceColourMeaning : Bool
    perSliceMinMaxPreservesCrossSliceColourMeaningIsFalse :
      perSliceMinMaxPreservesCrossSliceColourMeaning ≡ false

open FiveClassSimplexColourBoundary public

canonicalFiveClassSimplexColourBoundary :
  FiveClassSimplexColourBoundary
canonicalFiveClassSimplexColourBoundary =
  fiveClassSimplexColourBoundary
    false refl
    false refl
    false refl
    false refl
