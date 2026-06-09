module DASHI.Physics.Closure.QuantumClockSuperpositionReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Quantum clock superposition receipt.
--
-- This is a concrete constructive receipt for the fetched
-- "Quantum Time Superposition" thread.  It records the narrow formal
-- reading: a clock may be prepared in a coherent quantum state whose
-- branches carry different proper-time readings as observable labels.
--
-- The surface deliberately does not inhabit literal time splitting,
-- universe splitting, dynamical spacetime branching, or a full GR/QFT clock
-- theorem.  Proper time appears here as branch-carried observable data.

data ⊥ : Set where

data _∈_ {A : Set} (x : A) : List A → Set where
  here :
    {xs : List A} →
    x ∈ (x ∷ xs)

  there :
    {y : A} →
    {xs : List A} →
    x ∈ xs →
    x ∈ (y ∷ xs)

------------------------------------------------------------------------
-- Finite carriers.

data ClockArm : Set where
  lowerArm : ClockArm
  upperArm : ClockArm
  referenceArm : ClockArm

canonicalClockArms : List ClockArm
canonicalClockArms =
  lowerArm
  ∷ upperArm
  ∷ referenceArm
  ∷ []

lowerArmListed : lowerArm ∈ canonicalClockArms
lowerArmListed = here

upperArmListed : upperArm ∈ canonicalClockArms
upperArmListed = there here

referenceArmListed : referenceArm ∈ canonicalClockArms
referenceArmListed = there (there here)

data ProperTimeReading : Set where
  lowerElapsedTime : ProperTimeReading
  upperElapsedTime : ProperTimeReading
  referenceElapsedTime : ProperTimeReading

canonicalProperTimeReadings : List ProperTimeReading
canonicalProperTimeReadings =
  lowerElapsedTime
  ∷ upperElapsedTime
  ∷ referenceElapsedTime
  ∷ []

lowerElapsedTimeListed :
  lowerElapsedTime ∈ canonicalProperTimeReadings
lowerElapsedTimeListed = here

upperElapsedTimeListed :
  upperElapsedTime ∈ canonicalProperTimeReadings
upperElapsedTimeListed = there here

referenceElapsedTimeListed :
  referenceElapsedTime ∈ canonicalProperTimeReadings
referenceElapsedTimeListed = there (there here)

properTimeOfArm : ClockArm → ProperTimeReading
properTimeOfArm lowerArm = lowerElapsedTime
properTimeOfArm upperArm = upperElapsedTime
properTimeOfArm referenceArm = referenceElapsedTime

properTimeOfLowerArm :
  properTimeOfArm lowerArm ≡ lowerElapsedTime
properTimeOfLowerArm = refl

properTimeOfUpperArm :
  properTimeOfArm upperArm ≡ upperElapsedTime
properTimeOfUpperArm = refl

properTimeOfReferenceArm :
  properTimeOfArm referenceArm ≡ referenceElapsedTime
properTimeOfReferenceArm = refl

data ClockPreparation : Set where
  coherentProperTimeSuperposition : ClockPreparation
  incoherentClockMixture : ClockPreparation
  referenceClockControl : ClockPreparation

canonicalClockPreparations : List ClockPreparation
canonicalClockPreparations =
  coherentProperTimeSuperposition
  ∷ incoherentClockMixture
  ∷ referenceClockControl
  ∷ []

coherentPreparationListed :
  coherentProperTimeSuperposition ∈ canonicalClockPreparations
coherentPreparationListed = here

data ObservableSurfaceKind : Set where
  quantumCarriedProperTimeObservable : ObservableSurfaceKind
  classicalMixtureProperTimeObservable : ObservableSurfaceKind
  referenceClockObservable : ObservableSurfaceKind

observableSurfaceOfPreparation :
  ClockPreparation → ObservableSurfaceKind
observableSurfaceOfPreparation coherentProperTimeSuperposition =
  quantumCarriedProperTimeObservable
observableSurfaceOfPreparation incoherentClockMixture =
  classicalMixtureProperTimeObservable
observableSurfaceOfPreparation referenceClockControl =
  referenceClockObservable

coherentPreparationIsQuantumCarriedObservable :
  observableSurfaceOfPreparation coherentProperTimeSuperposition ≡
  quantumCarriedProperTimeObservable
coherentPreparationIsQuantumCarriedObservable = refl

data ClockReadoutQuotient : Set where
  interferometricPhaseQuotient : ClockReadoutQuotient
  whichArmClockQuotient : ClockReadoutQuotient
  ensembleHistogramQuotient : ClockReadoutQuotient

canonicalClockReadoutQuotients : List ClockReadoutQuotient
canonicalClockReadoutQuotients =
  interferometricPhaseQuotient
  ∷ whichArmClockQuotient
  ∷ ensembleHistogramQuotient
  ∷ []

data SuperpositionComponent : Set where
  lowerComponent : SuperpositionComponent
  upperComponent : SuperpositionComponent

componentArm : SuperpositionComponent → ClockArm
componentArm lowerComponent = lowerArm
componentArm upperComponent = upperArm

componentProperTime : SuperpositionComponent → ProperTimeReading
componentProperTime component =
  properTimeOfArm (componentArm component)

lowerComponentCarriesLowerProperTime :
  componentProperTime lowerComponent ≡ lowerElapsedTime
lowerComponentCarriesLowerProperTime = refl

upperComponentCarriesUpperProperTime :
  componentProperTime upperComponent ≡ upperElapsedTime
upperComponentCarriesUpperProperTime = refl

canonicalSuperpositionComponents : List SuperpositionComponent
canonicalSuperpositionComponents =
  lowerComponent
  ∷ upperComponent
  ∷ []

lowerComponentListed :
  lowerComponent ∈ canonicalSuperpositionComponents
lowerComponentListed = here

upperComponentListed :
  upperComponent ∈ canonicalSuperpositionComponents
upperComponentListed = there here

------------------------------------------------------------------------
-- Receipt records.

record QuantumClockBranchReceipt : Set where
  field
    component :
      SuperpositionComponent

    listedComponent :
      component ∈ canonicalSuperpositionComponents

    arm :
      ClockArm

    armIsComponentArm :
      arm ≡ componentArm component

    properTime :
      ProperTimeReading

    properTimeIsCarriedByArm :
      properTime ≡ properTimeOfArm arm

    reading :
      String

open QuantumClockBranchReceipt public

lowerBranchReceipt : QuantumClockBranchReceipt
lowerBranchReceipt =
  record
    { component =
        lowerComponent
    ; listedComponent =
        lowerComponentListed
    ; arm =
        lowerArm
    ; armIsComponentArm =
        refl
    ; properTime =
        lowerElapsedTime
    ; properTimeIsCarriedByArm =
        refl
    ; reading =
        "lower quantum-clock component carries the lower-arm proper-time observable"
    }

upperBranchReceipt : QuantumClockBranchReceipt
upperBranchReceipt =
  record
    { component =
        upperComponent
    ; listedComponent =
        upperComponentListed
    ; arm =
        upperArm
    ; armIsComponentArm =
        refl
    ; properTime =
        upperElapsedTime
    ; properTimeIsCarriedByArm =
        refl
    ; reading =
        "upper quantum-clock component carries the upper-arm proper-time observable"
    }

data QuantumClockNonPromotionBoundary : Set where
  noLiteralExternalTimeSplit : QuantumClockNonPromotionBoundary
  noLiteralUniverseSplit : QuantumClockNonPromotionBoundary
  noDynamicalSpacetimeBranchingTheorem : QuantumClockNonPromotionBoundary
  noGRQFTClockCompletionTheorem : QuantumClockNonPromotionBoundary
  noTimeTravelOrRetrocausalUpdateClaim : QuantumClockNonPromotionBoundary

canonicalQuantumClockBoundaries :
  List QuantumClockNonPromotionBoundary
canonicalQuantumClockBoundaries =
  noLiteralExternalTimeSplit
  ∷ noLiteralUniverseSplit
  ∷ noDynamicalSpacetimeBranchingTheorem
  ∷ noGRQFTClockCompletionTheorem
  ∷ noTimeTravelOrRetrocausalUpdateClaim
  ∷ []

noLiteralExternalTimeSplitListed :
  noLiteralExternalTimeSplit ∈ canonicalQuantumClockBoundaries
noLiteralExternalTimeSplitListed = here

noLiteralUniverseSplitListed :
  noLiteralUniverseSplit ∈ canonicalQuantumClockBoundaries
noLiteralUniverseSplitListed = there here

data LiteralExternalTimeSplitReceipt : Set where

data LiteralUniverseSplitReceipt : Set where

literalExternalTimeSplitBlocked :
  LiteralExternalTimeSplitReceipt → ⊥
literalExternalTimeSplitBlocked ()

literalUniverseSplitBlocked :
  LiteralUniverseSplitReceipt → ⊥
literalUniverseSplitBlocked ()

record QuantumClockSuperpositionReceipt : Set where
  field
    preparation :
      ClockPreparation

    preparationListed :
      preparation ∈ canonicalClockPreparations

    observableSurface :
      ObservableSurfaceKind

    observableSurfaceIsPreparationSurface :
      observableSurface ≡ observableSurfaceOfPreparation preparation

    readoutQuotient :
      ClockReadoutQuotient

    lowerReceipt :
      QuantumClockBranchReceipt

    upperReceipt :
      QuantumClockBranchReceipt

    lowerCarriesLowerProperTime :
      QuantumClockBranchReceipt.properTime lowerReceipt ≡ lowerElapsedTime

    upperCarriesUpperProperTime :
      QuantumClockBranchReceipt.properTime upperReceipt ≡ upperElapsedTime

    properTimeIsObservableData :
      Bool

    properTimeIsObservableDataIsTrue :
      properTimeIsObservableData ≡ true

    externalTimeSplitImplemented :
      Bool

    externalTimeSplitImplementedIsFalse :
      externalTimeSplitImplemented ≡ false

    universeSplitImplemented :
      Bool

    universeSplitImplementedIsFalse :
      universeSplitImplemented ≡ false

    externalTimeSplitReceiptBlocked :
      LiteralExternalTimeSplitReceipt → ⊥

    universeSplitReceiptBlocked :
      LiteralUniverseSplitReceipt → ⊥

    boundaries :
      List QuantumClockNonPromotionBoundary

    reading :
      String

open QuantumClockSuperpositionReceipt public

canonicalQuantumClockSuperpositionReceipt :
  QuantumClockSuperpositionReceipt
canonicalQuantumClockSuperpositionReceipt =
  record
    { preparation =
        coherentProperTimeSuperposition
    ; preparationListed =
        coherentPreparationListed
    ; observableSurface =
        quantumCarriedProperTimeObservable
    ; observableSurfaceIsPreparationSurface =
        refl
    ; readoutQuotient =
        interferometricPhaseQuotient
    ; lowerReceipt =
        lowerBranchReceipt
    ; upperReceipt =
        upperBranchReceipt
    ; lowerCarriesLowerProperTime =
        refl
    ; upperCarriesUpperProperTime =
        refl
    ; properTimeIsObservableData =
        true
    ; properTimeIsObservableDataIsTrue =
        refl
    ; externalTimeSplitImplemented =
        false
    ; externalTimeSplitImplementedIsFalse =
        refl
    ; universeSplitImplemented =
        false
    ; universeSplitImplementedIsFalse =
        refl
    ; externalTimeSplitReceiptBlocked =
        literalExternalTimeSplitBlocked
    ; universeSplitReceiptBlocked =
        literalUniverseSplitBlocked
    ; boundaries =
        canonicalQuantumClockBoundaries
    ; reading =
        "proper-time superposition is represented as quantum-carried observable data on finite clock branches, not as literal time or universe splitting"
    }

canonicalReceiptUsesCoherentPreparation :
  preparation canonicalQuantumClockSuperpositionReceipt ≡
  coherentProperTimeSuperposition
canonicalReceiptUsesCoherentPreparation = refl

canonicalReceiptUsesQuantumObservableSurface :
  observableSurface canonicalQuantumClockSuperpositionReceipt ≡
  quantumCarriedProperTimeObservable
canonicalReceiptUsesQuantumObservableSurface = refl

canonicalReceiptDoesNotImplementExternalTimeSplit :
  externalTimeSplitImplemented canonicalQuantumClockSuperpositionReceipt ≡
  false
canonicalReceiptDoesNotImplementExternalTimeSplit = refl

canonicalReceiptDoesNotImplementUniverseSplit :
  universeSplitImplemented canonicalQuantumClockSuperpositionReceipt ≡
  false
canonicalReceiptDoesNotImplementUniverseSplit = refl

record QuantumClockSuperpositionValidation : Set where
  field
    receipt :
      QuantumClockSuperpositionReceipt

    coherentPreparationVerified :
      preparation receipt ≡ coherentProperTimeSuperposition

    quantumObservableSurfaceVerified :
      observableSurface receipt ≡ quantumCarriedProperTimeObservable

    lowerBranchProperTimeVerified :
      QuantumClockBranchReceipt.properTime (lowerReceipt receipt) ≡
      lowerElapsedTime

    upperBranchProperTimeVerified :
      QuantumClockBranchReceipt.properTime (upperReceipt receipt) ≡
      upperElapsedTime

    externalTimeSplitRejected :
      externalTimeSplitImplemented receipt ≡ false

    universeSplitRejected :
      universeSplitImplemented receipt ≡ false

    statedBoundaries :
      List QuantumClockNonPromotionBoundary

open QuantumClockSuperpositionValidation public

canonicalQuantumClockSuperpositionValidation :
  QuantumClockSuperpositionValidation
canonicalQuantumClockSuperpositionValidation =
  record
    { receipt =
        canonicalQuantumClockSuperpositionReceipt
    ; coherentPreparationVerified =
        refl
    ; quantumObservableSurfaceVerified =
        refl
    ; lowerBranchProperTimeVerified =
        refl
    ; upperBranchProperTimeVerified =
        refl
    ; externalTimeSplitRejected =
        refl
    ; universeSplitRejected =
        refl
    ; statedBoundaries =
        canonicalQuantumClockBoundaries
    }
