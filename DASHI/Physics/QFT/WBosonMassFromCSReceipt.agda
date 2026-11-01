module DASHI.Physics.QFT.WBosonMassFromCSReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.EWSBFromCSHiggsReceipt as EWSB
import DASHI.Physics.QFT.SMGaugeBosonsFromCSBoundaryReceipt as Bosons

------------------------------------------------------------------------
-- W-boson mass candidate from naive CS/WZW coupling.
--
-- This receipt records the numeric failure mode of the naive WZW k=1 coupling
-- estimate.  The candidate estimate gives M_W approximately 218 GeV, while
-- the physical comparison value is 80.37 GeV, recorded here as a 172 percent
-- relative error.  The gap is marked as requiring RG running / scale matching.
--
-- No exact W mass, exact electroweak fit, exact Standard Model, or terminal
-- promotion is asserted.

data WBosonMassEstimateMethod : Set where
  naiveWZWLevelOneCoupling :
    WBosonMassEstimateMethod

data WMassComparisonStatus : Set where
  numericallyInadequateWithoutRG :
    WMassComparisonStatus

data WMassCorrectionRequirement : Set where
  requiresRGRunningAndScaleMatching :
    WMassCorrectionRequirement

naiveWZWK1CouplingLabel : String
naiveWZWK1CouplingLabel =
  "Naive WZW k=1 coupling estimate for the W mass"

mwNaiveEstimateLabel : String
mwNaiveEstimateLabel =
  "M_W naive estimate approximately 218 GeV"

mwPhysicalReferenceLabel : String
mwPhysicalReferenceLabel =
  "M_W physical comparison value 80.37 GeV"

mwRelativeErrorLabel : String
mwRelativeErrorLabel =
  "Relative error approximately 172 percent"

rgRunningRequiredLabel : String
rgRunningRequiredLabel =
  "RG running and scale matching are required before any physical W-mass claim"

record WBosonMassFromCSReceipt : Setω where
  field
    gaugeBosonReceipt :
      Bosons.SMGaugeBosonsFromCSBoundaryReceipt

    wModesCandidateIsTrue :
      Bosons.SMGaugeBosonsFromCSBoundaryReceipt.wModesCandidate
        gaugeBosonReceipt
      ≡
      true

    ewsbReceipt :
      EWSB.EWSBFromCSHiggsReceipt

    exactWZMassSplittingStillFalse :
      EWSB.EWSBFromCSHiggsReceipt.exactWZMassSplittingConstructed
        ewsbReceipt
      ≡
      false

    estimateMethod :
      WBosonMassEstimateMethod

    estimateMethodIsNaiveWZWK1 :
      estimateMethod ≡ naiveWZWLevelOneCoupling

    estimateMethodStatement :
      String

    estimateMethodStatementIsCanonical :
      estimateMethodStatement ≡ naiveWZWK1CouplingLabel

    wzwLevel :
      Nat

    wzwLevelIsOne :
      wzwLevel ≡ 1

    naiveMassGeV :
      Nat

    naiveMassGeVIs218 :
      naiveMassGeV ≡ 218

    naiveMassStatement :
      String

    naiveMassStatementIsCanonical :
      naiveMassStatement ≡ mwNaiveEstimateLabel

    physicalMassReferenceStatement :
      String

    physicalMassReferenceStatementIsCanonical :
      physicalMassReferenceStatement ≡ mwPhysicalReferenceLabel

    relativeErrorPercent :
      Nat

    relativeErrorPercentIs172 :
      relativeErrorPercent ≡ 172

    relativeErrorStatement :
      String

    relativeErrorStatementIsCanonical :
      relativeErrorStatement ≡ mwRelativeErrorLabel

    comparisonStatus :
      WMassComparisonStatus

    comparisonStatusIsNumericallyInadequateWithoutRG :
      comparisonStatus ≡ numericallyInadequateWithoutRG

    correctionRequirement :
      WMassCorrectionRequirement

    correctionRequirementIsRGRunningAndScaleMatching :
      correctionRequirement ≡ requiresRGRunningAndScaleMatching

    rgRunningRequiredStatement :
      String

    rgRunningRequiredStatementIsCanonical :
      rgRunningRequiredStatement ≡ rgRunningRequiredLabel

    rgRunningConstructed :
      Bool

    rgRunningConstructedIsFalse :
      rgRunningConstructed ≡ false

    exactWMass :
      Bool

    exactWMassIsFalse :
      exactWMass ≡ false

    exactElectroweakFit :
      Bool

    exactElectroweakFitIsFalse :
      exactElectroweakFit ≡ false

    exactStandardModel :
      Bool

    exactStandardModelIsFalse :
      exactStandardModel ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    receiptBoundary :
      List String

open WBosonMassFromCSReceipt public

canonicalWBosonMassFromCSReceipt :
  WBosonMassFromCSReceipt
canonicalWBosonMassFromCSReceipt =
  record
    { gaugeBosonReceipt =
        Bosons.canonicalSMGaugeBosonsFromCSBoundaryReceipt
    ; wModesCandidateIsTrue =
        refl
    ; ewsbReceipt =
        EWSB.canonicalEWSBFromCSHiggsReceipt
    ; exactWZMassSplittingStillFalse =
        refl
    ; estimateMethod =
        naiveWZWLevelOneCoupling
    ; estimateMethodIsNaiveWZWK1 =
        refl
    ; estimateMethodStatement =
        naiveWZWK1CouplingLabel
    ; estimateMethodStatementIsCanonical =
        refl
    ; wzwLevel =
        1
    ; wzwLevelIsOne =
        refl
    ; naiveMassGeV =
        218
    ; naiveMassGeVIs218 =
        refl
    ; naiveMassStatement =
        mwNaiveEstimateLabel
    ; naiveMassStatementIsCanonical =
        refl
    ; physicalMassReferenceStatement =
        mwPhysicalReferenceLabel
    ; physicalMassReferenceStatementIsCanonical =
        refl
    ; relativeErrorPercent =
        172
    ; relativeErrorPercentIs172 =
        refl
    ; relativeErrorStatement =
        mwRelativeErrorLabel
    ; relativeErrorStatementIsCanonical =
        refl
    ; comparisonStatus =
        numericallyInadequateWithoutRG
    ; comparisonStatusIsNumericallyInadequateWithoutRG =
        refl
    ; correctionRequirement =
        requiresRGRunningAndScaleMatching
    ; correctionRequirementIsRGRunningAndScaleMatching =
        refl
    ; rgRunningRequiredStatement =
        rgRunningRequiredLabel
    ; rgRunningRequiredStatementIsCanonical =
        refl
    ; rgRunningConstructed =
        false
    ; rgRunningConstructedIsFalse =
        refl
    ; exactWMass =
        false
    ; exactWMassIsFalse =
        refl
    ; exactElectroweakFit =
        false
    ; exactElectroweakFitIsFalse =
        refl
    ; exactStandardModel =
        false
    ; exactStandardModelIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; receiptBoundary =
        "Naive WZW k=1 coupling gives M_W approximately 218 GeV"
        ∷ "Physical comparison value is recorded as 80.37 GeV"
        ∷ "The relative error is recorded as approximately 172 percent"
        ∷ "RG running and scale matching are required; exact W mass remains false"
        ∷ []
    }

wBosonMassNaiveEstimateIs218 :
  naiveMassGeV canonicalWBosonMassFromCSReceipt
  ≡
  218
wBosonMassNaiveEstimateIs218 =
  refl

wBosonMassRelativeErrorIs172 :
  relativeErrorPercent canonicalWBosonMassFromCSReceipt
  ≡
  172
wBosonMassRelativeErrorIs172 =
  refl

wBosonMassRGRunningConstructedFalse :
  rgRunningConstructed canonicalWBosonMassFromCSReceipt
  ≡
  false
wBosonMassRGRunningConstructedFalse =
  refl

wBosonMassExactWMassFalse :
  exactWMass canonicalWBosonMassFromCSReceipt
  ≡
  false
wBosonMassExactWMassFalse =
  refl
