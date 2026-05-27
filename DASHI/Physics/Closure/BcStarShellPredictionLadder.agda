module DASHI.Physics.Closure.BcStarShellPredictionLadder where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_; _-_)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Bc*+ / Bc+ shell-prediction ladder receipt.
--
-- This is a concrete pre-look, axiom-free receipt for a deliberately
-- narrow observable: the toy natural-unit energy delta between the
-- vector-labelled Bc*+ shell and the pseudoscalar-labelled Bc+ shell on
-- the fixed (c, anti-b) carrier.  It records a frozen parameter packet and
-- blocks promotion until an empirical comparison receipt is supplied
-- elsewhere.

data ElectricChargeLabel : Set where
  plusCharge :
    ElectricChargeLabel

data QuarkConstituent : Set where
  charmQuark :
    QuarkConstituent
  antiBottomQuark :
    QuarkConstituent

record BcMesonCarrier : Set where
  field
    firstLeg :
      QuarkConstituent

    secondLeg :
      QuarkConstituent

    charge :
      ElectricChargeLabel

open BcMesonCarrier public

bcPlusCarrier :
  BcMesonCarrier
bcPlusCarrier =
  record
    { firstLeg =
        charmQuark
    ; secondLeg =
        antiBottomQuark
    ; charge =
        plusCharge
    }

bcPlusCarrierIsCharmAntiBottom :
  firstLeg bcPlusCarrier ≡ charmQuark
bcPlusCarrierIsCharmAntiBottom =
  refl

bcPlusCarrierSecondLegIsAntiBottom :
  secondLeg bcPlusCarrier ≡ antiBottomQuark
bcPlusCarrierSecondLegIsAntiBottom =
  refl

data BcShellLabel : Set where
  bcPlusGroundPseudoscalar :
    BcShellLabel
  bcStarPlusVectorExcited :
    BcShellLabel

data NarrowBcObservable : Set where
  bcStarMinusBcGroundEnergyDelta :
    NarrowBcObservable

shellQuantumNumber :
  BcShellLabel →
  Nat
shellQuantumNumber bcPlusGroundPseudoscalar =
  0
shellQuantumNumber bcStarPlusVectorExcited =
  1

spinPenaltyToy :
  BcShellLabel →
  Nat
spinPenaltyToy bcPlusGroundPseudoscalar =
  0
spinPenaltyToy bcStarPlusVectorExcited =
  7

record ToyEnergyParameters : Set where
  field
    charmRestToy :
      Nat

    antiBottomRestToy :
      Nat

    sharedBindingToy :
      Nat

    shellSpacingToy :
      Nat

    spinSplittingToy :
      Nat

open ToyEnergyParameters public

frozenBcToyEnergyParameters :
  ToyEnergyParameters
frozenBcToyEnergyParameters =
  record
    { charmRestToy =
        1500
    ; antiBottomRestToy =
        4800
    ; sharedBindingToy =
        25
    ; shellSpacingToy =
        35
    ; spinSplittingToy =
        1
    }

toyShellEnergy :
  ToyEnergyParameters →
  BcMesonCarrier →
  BcShellLabel →
  Nat
toyShellEnergy params carrier shell =
  charmRestToy params
  + antiBottomRestToy params
  + sharedBindingToy params
  + shellSpacingToy params * shellQuantumNumber shell
  + spinSplittingToy params * spinPenaltyToy shell

bcPlusToyGroundEnergy :
  Nat
bcPlusToyGroundEnergy =
  toyShellEnergy
    frozenBcToyEnergyParameters
    bcPlusCarrier
    bcPlusGroundPseudoscalar

bcStarPlusToyExcitedEnergy :
  Nat
bcStarPlusToyExcitedEnergy =
  toyShellEnergy
    frozenBcToyEnergyParameters
    bcPlusCarrier
    bcStarPlusVectorExcited

toyDeltaEnergy :
  ToyEnergyParameters →
  BcMesonCarrier →
  Nat
toyDeltaEnergy params carrier =
  toyShellEnergy params carrier bcStarPlusVectorExcited
  -
  toyShellEnergy params carrier bcPlusGroundPseudoscalar

bcStarBcToyDeltaEnergy :
  Nat
bcStarBcToyDeltaEnergy =
  toyDeltaEnergy frozenBcToyEnergyParameters bcPlusCarrier

bcPlusToyGroundEnergyIs6325 :
  bcPlusToyGroundEnergy ≡ 6325
bcPlusToyGroundEnergyIs6325 =
  refl

bcStarPlusToyExcitedEnergyIs6367 :
  bcStarPlusToyExcitedEnergy ≡ 6367
bcStarPlusToyExcitedEnergyIs6367 =
  refl

bcStarBcToyDeltaEnergyIs42 :
  bcStarBcToyDeltaEnergy ≡ 42
bcStarBcToyDeltaEnergyIs42 =
  refl

data PredictionLookState : Set where
  preEmpiricalLook :
    PredictionLookState

data ParameterFreezeState : Set where
  frozenBeforeEmpiricalComparison :
    ParameterFreezeState

data BcPredictionPromotionStatus : Set where
  candidateOnlyAwaitingEmpiricalComparison :
    BcPredictionPromotionStatus

data BcEmpiricalComparisonReceipt : Set where

empiricalComparisonReceiptImpossibleHere :
  BcEmpiricalComparisonReceipt →
  ⊥
empiricalComparisonReceiptImpossibleHere ()

data BcEmpiricalPromotionToken : Set where

empiricalPromotionTokenImpossibleHere :
  BcEmpiricalPromotionToken →
  ⊥
empiricalPromotionTokenImpossibleHere ()

data BcPredictionBoundary : Set where
  noPhysicalMassCalibration :
    BcPredictionBoundary
  noQCDPotentialClaim :
    BcPredictionBoundary
  noDatasetLookahead :
    BcPredictionBoundary
  noEmpiricalComparisonReceipt :
    BcPredictionBoundary
  noPromotionBeforeComparison :
    BcPredictionBoundary

canonicalBcPredictionBoundaries :
  List BcPredictionBoundary
canonicalBcPredictionBoundaries =
  noPhysicalMassCalibration
  ∷ noQCDPotentialClaim
  ∷ noDatasetLookahead
  ∷ noEmpiricalComparisonReceipt
  ∷ noPromotionBeforeComparison
  ∷ []

record BcStarShellPredictionLadderReceipt : Setω where
  field
    observable :
      NarrowBcObservable

    carrier :
      BcMesonCarrier

    carrierFirstLegIsCharm :
      firstLeg carrier ≡ charmQuark

    carrierSecondLegIsAntiBottom :
      secondLeg carrier ≡ antiBottomQuark

    groundShell :
      BcShellLabel

    excitedShell :
      BcShellLabel

    groundShellIsBcPlus :
      groundShell ≡ bcPlusGroundPseudoscalar

    excitedShellIsBcStarPlus :
      excitedShell ≡ bcStarPlusVectorExcited

    parameters :
      ToyEnergyParameters

    parameterFreezeState :
      ParameterFreezeState

    lookState :
      PredictionLookState

    parametersFrozen :
      Bool

    parametersFrozenIsTrue :
      parametersFrozen ≡ true

    empiricalDataInspected :
      Bool

    empiricalDataInspectedIsFalse :
      empiricalDataInspected ≡ false

    toyEnergyFunctional :
      ToyEnergyParameters →
      BcMesonCarrier →
      BcShellLabel →
      Nat

    toyEnergyFunctionalIsCanonical :
      toyEnergyFunctional ≡ toyShellEnergy

    predictedGroundEnergy :
      Nat

    predictedGroundEnergyIsCanonical :
      predictedGroundEnergy
      ≡
      toyShellEnergy parameters carrier groundShell

    predictedExcitedEnergy :
      Nat

    predictedExcitedEnergyIsCanonical :
      predictedExcitedEnergy
      ≡
      toyShellEnergy parameters carrier excitedShell

    predictedDeltaEnergy :
      Nat

    predictedDeltaEnergyIsCanonical :
      predictedDeltaEnergy
      ≡
      toyShellEnergy parameters carrier excitedShell
      -
      toyShellEnergy parameters carrier groundShell

    canonicalDeltaValue :
      predictedDeltaEnergy ≡ 42

    comparisonReceiptBlocked :
      BcEmpiricalComparisonReceipt →
      ⊥

    promotionStatus :
      BcPredictionPromotionStatus

    promotionClaimed :
      Bool

    promotionClaimedIsFalse :
      promotionClaimed ≡ false

    promotionTokenBlocked :
      BcEmpiricalPromotionToken →
      ⊥

    boundary :
      List BcPredictionBoundary

    boundaryIsCanonical :
      boundary ≡ canonicalBcPredictionBoundaries

    receiptText :
      List String

open BcStarShellPredictionLadderReceipt public

canonicalBcStarShellPredictionLadderReceipt :
  BcStarShellPredictionLadderReceipt
canonicalBcStarShellPredictionLadderReceipt =
  record
    { observable =
        bcStarMinusBcGroundEnergyDelta
    ; carrier =
        bcPlusCarrier
    ; carrierFirstLegIsCharm =
        refl
    ; carrierSecondLegIsAntiBottom =
        refl
    ; groundShell =
        bcPlusGroundPseudoscalar
    ; excitedShell =
        bcStarPlusVectorExcited
    ; groundShellIsBcPlus =
        refl
    ; excitedShellIsBcStarPlus =
        refl
    ; parameters =
        frozenBcToyEnergyParameters
    ; parameterFreezeState =
        frozenBeforeEmpiricalComparison
    ; lookState =
        preEmpiricalLook
    ; parametersFrozen =
        true
    ; parametersFrozenIsTrue =
        refl
    ; empiricalDataInspected =
        false
    ; empiricalDataInspectedIsFalse =
        refl
    ; toyEnergyFunctional =
        toyShellEnergy
    ; toyEnergyFunctionalIsCanonical =
        refl
    ; predictedGroundEnergy =
        bcPlusToyGroundEnergy
    ; predictedGroundEnergyIsCanonical =
        refl
    ; predictedExcitedEnergy =
        bcStarPlusToyExcitedEnergy
    ; predictedExcitedEnergyIsCanonical =
        refl
    ; predictedDeltaEnergy =
        bcStarBcToyDeltaEnergy
    ; predictedDeltaEnergyIsCanonical =
        refl
    ; canonicalDeltaValue =
        refl
    ; comparisonReceiptBlocked =
        empiricalComparisonReceiptImpossibleHere
    ; promotionStatus =
        candidateOnlyAwaitingEmpiricalComparison
    ; promotionClaimed =
        false
    ; promotionClaimedIsFalse =
        refl
    ; promotionTokenBlocked =
        empiricalPromotionTokenImpossibleHere
    ; boundary =
        canonicalBcPredictionBoundaries
    ; boundaryIsCanonical =
        refl
    ; receiptText =
        "Observable: delta E toy(Bc*+) - toy(Bc+) only"
        ∷ "Carrier: fixed plus charged charm and anti-bottom pair"
        ∷ "Ground shell label: Bc+ pseudoscalar"
        ∷ "Excited shell label: Bc*+ vector"
        ∷ "Frozen toy parameters: charm 1500, anti-bottom 4800, binding 25, shell spacing 35, spin unit 1"
        ∷ "Computed toy energies: ground 6325, excited 6367, delta 42"
        ∷ "Pre-look guard: empiricalDataInspected is false"
        ∷ "No physical calibration, QCD potential claim, empirical comparison, or promotion token is constructed"
        ∷ []
    }

canonicalBcStarPredictionPromotionStatus :
  BcPredictionPromotionStatus
canonicalBcStarPredictionPromotionStatus =
  promotionStatus canonicalBcStarShellPredictionLadderReceipt

canonicalBcStarPredictionDelta :
  Nat
canonicalBcStarPredictionDelta =
  predictedDeltaEnergy canonicalBcStarShellPredictionLadderReceipt

canonicalBcStarPredictionDeltaIs42 :
  canonicalBcStarPredictionDelta ≡ 42
canonicalBcStarPredictionDeltaIs42 =
  refl
