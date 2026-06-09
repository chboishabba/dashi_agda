module DASHI.Physics.Closure.CarrierScaleFromHeegnerReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CarrierLatticeYMDefinitionReceipt as Lattice

data CarrierScaleFromHeegnerStatus : Set where
  heegnerCarrierScaleRecordedNoPhysicalAnchor :
    CarrierScaleFromHeegnerStatus

data HeegnerCarrierScaleInput : Set where
  p2GaussianLane :
    HeegnerCarrierScaleInput

  p3EisensteinLane :
    HeegnerCarrierScaleInput

  p5DiscriminantMinusSevenLane :
    HeegnerCarrierScaleInput

  depthExponentD :
    HeegnerCarrierScaleInput

canonicalHeegnerCarrierScaleInputs :
  List HeegnerCarrierScaleInput
canonicalHeegnerCarrierScaleInputs =
  p2GaussianLane
  ∷ p3EisensteinLane
  ∷ p5DiscriminantMinusSevenLane
  ∷ depthExponentD
  ∷ []

data CarrierScaleBlocker : Set where
  missingDimensionfulUnitAnchor :
    CarrierScaleBlocker

  missingLambdaQCDIdentification :
    CarrierScaleBlocker

  missingContinuumSpacingLimit :
    CarrierScaleBlocker

canonicalCarrierScaleBlockers :
  List CarrierScaleBlocker
canonicalCarrierScaleBlockers =
  missingDimensionfulUnitAnchor
  ∷ missingLambdaQCDIdentification
  ∷ missingContinuumSpacingLimit
  ∷ []

data CarrierScalePromotion : Set where

carrierScalePromotionImpossibleHere :
  CarrierScalePromotion →
  ⊥
carrierScalePromotionImpossibleHere ()

carrierScaleFormulaLabel : String
carrierScaleFormulaLabel =
  "a_d = alpha1^d from Heegner carrier depth"

carrierScaleBoundaryLabel : String
carrierScaleBoundaryLabel =
  "Heegner depth supplies a dimensionless carrier spacing label, not a GeV scale or Lambda_QCD anchor"

carrierScaleEstimateLabel : String
carrierScaleEstimateLabel =
  "sqrt(2 GeV * 1.27 GeV) = 1.59 GeV"

record CarrierScaleFromHeegnerReceipt : Setω where
  field
    status :
      CarrierScaleFromHeegnerStatus

    latticeReceipt :
      Lattice.CarrierLatticeYMDefinitionReceipt

    latticeSpacingMatchesCarrier :
      Lattice.latticeSpacingLabel latticeReceipt ≡ "alpha1^d"

    heegnerLaneCount :
      Nat

    heegnerLaneCountIsThree :
      heegnerLaneCount ≡ 3

    carrierDepthRecorded :
      Bool

    carrierDepthRecordedIsTrue :
      carrierDepthRecorded ≡ true

    scaleFormula :
      String

    scaleFormulaIsCanonical :
      scaleFormula ≡ carrierScaleFormulaLabel

    boundaryStatement :
      String

    boundaryStatementIsCanonical :
      boundaryStatement ≡ carrierScaleBoundaryLabel

    dimensionlessCarrierScaleRecorded :
      Bool

    dimensionlessCarrierScaleRecordedIsTrue :
      dimensionlessCarrierScaleRecorded ≡ true

    carrierScaleEstimate :
      String

    carrierScaleEstimateIsCanonical :
      carrierScaleEstimate ≡ carrierScaleEstimateLabel

    carrierScaleNearCharmMass :
      Bool

    carrierScaleNearCharmMassIsTrue :
      carrierScaleNearCharmMass ≡ true

    dimensionfulCarrierScaleDerived :
      Bool

    dimensionfulCarrierScaleDerivedIsFalse :
      dimensionfulCarrierScaleDerived ≡ false

    qcdScaleAnchorDerived :
      Bool

    qcdScaleAnchorDerivedIsFalse :
      qcdScaleAnchorDerived ≡ false

    continuumYangMillsConstructed :
      Bool

    continuumYangMillsConstructedIsFalse :
      continuumYangMillsConstructed ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    inputs :
      List HeegnerCarrierScaleInput

    inputsAreCanonical :
      inputs ≡ canonicalHeegnerCarrierScaleInputs

    blockers :
      List CarrierScaleBlocker

    blockersAreCanonical :
      blockers ≡ canonicalCarrierScaleBlockers

    promotionFlags :
      List CarrierScalePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open CarrierScaleFromHeegnerReceipt public

canonicalCarrierScaleFromHeegnerReceipt :
  CarrierScaleFromHeegnerReceipt
canonicalCarrierScaleFromHeegnerReceipt =
  record
    { status =
        heegnerCarrierScaleRecordedNoPhysicalAnchor
    ; latticeReceipt =
        Lattice.canonicalCarrierLatticeYMDefinitionReceipt
    ; latticeSpacingMatchesCarrier =
        refl
    ; heegnerLaneCount =
        3
    ; heegnerLaneCountIsThree =
        refl
    ; carrierDepthRecorded =
        true
    ; carrierDepthRecordedIsTrue =
        refl
    ; scaleFormula =
        carrierScaleFormulaLabel
    ; scaleFormulaIsCanonical =
        refl
    ; boundaryStatement =
        carrierScaleBoundaryLabel
    ; boundaryStatementIsCanonical =
        refl
    ; dimensionlessCarrierScaleRecorded =
        true
    ; dimensionlessCarrierScaleRecordedIsTrue =
        refl
    ; carrierScaleEstimate =
        carrierScaleEstimateLabel
    ; carrierScaleEstimateIsCanonical =
        refl
    ; carrierScaleNearCharmMass =
        true
    ; carrierScaleNearCharmMassIsTrue =
        refl
    ; dimensionfulCarrierScaleDerived =
        false
    ; dimensionfulCarrierScaleDerivedIsFalse =
        refl
    ; qcdScaleAnchorDerived =
        false
    ; qcdScaleAnchorDerivedIsFalse =
        refl
    ; continuumYangMillsConstructed =
        false
    ; continuumYangMillsConstructedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; inputs =
        canonicalHeegnerCarrierScaleInputs
    ; inputsAreCanonical =
        refl
    ; blockers =
        canonicalCarrierScaleBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

carrierScaleFromHeegnerKeepsClayFalse :
  clayYangMillsPromoted canonicalCarrierScaleFromHeegnerReceipt ≡ false
carrierScaleFromHeegnerKeepsClayFalse =
  refl
