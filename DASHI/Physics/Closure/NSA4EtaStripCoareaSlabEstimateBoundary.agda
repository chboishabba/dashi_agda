module DASHI.Physics.Closure.NSA4EtaStripCoareaSlabEstimateBoundary where

-- NS A4 boundary: eta-strip coarea slab estimate.
--
-- This module isolates the quantitative slab estimate used inside A4:
--
--   S_{n,eta} = { c in S2 : |c . n| <= eta }
--
-- pulled back under
--
--   Phi(theta1,theta2) = normalize(theta1 + theta2)
--
-- on the non-antipodal product-angular domain.  The intended theorem is
-- that the slab has a uniform positive lower term c_A4 * eta after
-- subtracting the antipodal, Sard/critical, rank-drop, packet-boundary,
-- and log-window errors.  This file records that theorem shape and its
-- fail-closed dependencies only.  It proves no coarea theorem, no Sard
-- theorem, no antipodal tube estimate, no uniform constant theorem, no
-- output-strip preimage theorem, no A4/A6 theorem, no Navier-Stokes Clay
-- result, and no terminal promotion.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSA4UniformInNormalConstantsBoundary
  as UniformNormal
import DASHI.Physics.Closure.NSAntipodalTubeNullMassBoundary
  as Antipodal
import DASHI.Physics.Closure.NSOutputStripPreimageMeasureEstimateBoundary
  as OutputPreimage
import DASHI.Physics.Closure.NSSardRegularValueSlicingBoundary
  as Sard

------------------------------------------------------------------------
-- Local utilities.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Imported support.

record ImportedEtaStripCoareaSlabSupport : Set where
  field
    outputPreimageBoundary :
      OutputPreimage.NSOutputStripPreimageMeasureEstimateBoundary
    outputPreimageBoundaryIsCanonical :
      outputPreimageBoundary
        ≡ OutputPreimage.canonicalNSOutputStripPreimageMeasureEstimateBoundary
    sardBoundary :
      Sard.NSSardRegularValueSlicingBoundary
    sardBoundaryIsCanonical :
      sardBoundary
        ≡ Sard.canonicalNSSardRegularValueSlicingBoundary
    antipodalBoundary :
      Antipodal.NSAntipodalTubeNullMassBoundary
    antipodalBoundaryIsCanonical :
      antipodalBoundary
        ≡ Antipodal.canonicalNSAntipodalTubeNullMassBoundary
    uniformNormalBoundary :
      UniformNormal.NSA4UniformInNormalConstantsBoundary
    uniformNormalBoundaryIsCanonical :
      uniformNormalBoundary
        ≡ UniformNormal.canonicalNSA4UniformInNormalConstantsBoundary

    outputPreimageTarget :
      OutputPreimage.OutputStripPreimageMeasureEstimateTarget
    outputPreimageTargetIsCanonical :
      outputPreimageTarget
        ≡ OutputPreimage.canonicalOutputStripPreimageMeasureEstimateTarget
    outputStripTest :
      OutputPreimage.OutputGreatCircleStripTestCarrier
    outputStripTestIsCanonical :
      outputStripTest
        ≡ OutputPreimage.canonicalOutputGreatCircleStripTestCarrier
    phiPreimage :
      OutputPreimage.PhiNormalizeSumPreimageCarrier
    phiPreimageIsCanonical :
      phiPreimage
        ≡ OutputPreimage.canonicalPhiNormalizeSumPreimageCarrier
    preimageDomain :
      OutputPreimage.PreimageMeasureDomainCarrier
    preimageDomainIsCanonical :
      preimageDomain
        ≡ OutputPreimage.canonicalPreimageMeasureDomainCarrier
    stripWidthJacobianBudget :
      OutputPreimage.StripWidthJacobianBudgetCarrier
    stripWidthJacobianBudgetIsCanonical :
      stripWidthJacobianBudget
        ≡ OutputPreimage.canonicalStripWidthJacobianBudgetCarrier
    nullExceptionalBudget :
      OutputPreimage.NullExceptionalBudgetCarrier
    nullExceptionalBudgetIsCanonical :
      nullExceptionalBudget
        ≡ OutputPreimage.canonicalNullExceptionalBudgetCarrier

    sardTarget :
      Sard.SardRegularValueSlicingTarget
    sardTargetIsCanonical :
      sardTarget
        ≡ Sard.canonicalSardRegularValueSlicingTarget
    regularValueCarrier :
      Sard.RegularValueCarrier
    regularValueCarrierIsCanonical :
      regularValueCarrier
        ≡ Sard.canonicalRegularValueCarrier
    sardExceptionalSet :
      Sard.SardExceptionalSetCarrier
    sardExceptionalSetIsCanonical :
      sardExceptionalSet
        ≡ Sard.canonicalSardExceptionalSetCarrier
    stripSlicingEstimate :
      Sard.StripSlicingEstimateCarrier
    stripSlicingEstimateIsCanonical :
      stripSlicingEstimate
        ≡ Sard.canonicalStripSlicingEstimateCarrier

    antipodalTube :
      Antipodal.AntipodalTubeCarrier
    antipodalTubeIsCanonical :
      antipodalTube
        ≡ Antipodal.canonicalAntipodalTubeCarrier
    antipodalNullMassTarget :
      Antipodal.AntipodalTubeNullMassTarget
    antipodalNullMassTargetIsCanonical :
      antipodalNullMassTarget
        ≡ Antipodal.canonicalAntipodalTubeNullMassTarget
    normalizeSumDomain :
      Antipodal.NormalizeSumDomainExclusion
    normalizeSumDomainIsCanonical :
      normalizeSumDomain
        ≡ Antipodal.canonicalNormalizeSumDomainExclusion

    uniformNormalTarget :
      UniformNormal.UniformInNormalConstantsTarget
    uniformNormalTargetIsCanonical :
      uniformNormalTarget
        ≡ UniformNormal.canonicalUniformInNormalConstantsTarget
    cA4LowerBound :
      UniformNormal.LowerBoundConstantCA4Carrier
    cA4LowerBoundIsCanonical :
      cA4LowerBound
        ≡ UniformNormal.canonicalLowerBoundConstantCA4Carrier
    etaScaleSeparation :
      UniformNormal.EtaWindowScaleSeparationCarrier
    etaScaleSeparationIsCanonical :
      etaScaleSeparation
        ≡ UniformNormal.canonicalEtaWindowScaleSeparationCarrier
    uniformCoareaObligation :
      UniformNormal.UniformInNormalCoareaConstantObligationCarrier
    uniformCoareaObligationIsCanonical :
      uniformCoareaObligation
        ≡ UniformNormal.canonicalUniformInNormalCoareaConstantObligationCarrier

    outputPreimageStillFalse :
      OutputPreimage.OutputStripPreimageMeasureEstimateProved ≡ false
    sardStillFalse :
      Sard.SardRegularValueSlicingProved ≡ false
    antipodalStillFalse :
      Antipodal.antipodalTubeNullMassProved ≡ false
    uniformNormalStillFalse :
      UniformNormal.uniformInNormalConstantsTheoremProved ≡ false
    cA4StillFalse :
      UniformNormal.positiveLowerBoundConstantCA4Proved ≡ false

canonicalImportedEtaStripCoareaSlabSupport :
  ImportedEtaStripCoareaSlabSupport
canonicalImportedEtaStripCoareaSlabSupport =
  record
    { outputPreimageBoundary =
        OutputPreimage.canonicalNSOutputStripPreimageMeasureEstimateBoundary
    ; outputPreimageBoundaryIsCanonical =
        refl
    ; sardBoundary =
        Sard.canonicalNSSardRegularValueSlicingBoundary
    ; sardBoundaryIsCanonical =
        refl
    ; antipodalBoundary =
        Antipodal.canonicalNSAntipodalTubeNullMassBoundary
    ; antipodalBoundaryIsCanonical =
        refl
    ; uniformNormalBoundary =
        UniformNormal.canonicalNSA4UniformInNormalConstantsBoundary
    ; uniformNormalBoundaryIsCanonical =
        refl
    ; outputPreimageTarget =
        OutputPreimage.canonicalOutputStripPreimageMeasureEstimateTarget
    ; outputPreimageTargetIsCanonical =
        refl
    ; outputStripTest =
        OutputPreimage.canonicalOutputGreatCircleStripTestCarrier
    ; outputStripTestIsCanonical =
        refl
    ; phiPreimage =
        OutputPreimage.canonicalPhiNormalizeSumPreimageCarrier
    ; phiPreimageIsCanonical =
        refl
    ; preimageDomain =
        OutputPreimage.canonicalPreimageMeasureDomainCarrier
    ; preimageDomainIsCanonical =
        refl
    ; stripWidthJacobianBudget =
        OutputPreimage.canonicalStripWidthJacobianBudgetCarrier
    ; stripWidthJacobianBudgetIsCanonical =
        refl
    ; nullExceptionalBudget =
        OutputPreimage.canonicalNullExceptionalBudgetCarrier
    ; nullExceptionalBudgetIsCanonical =
        refl
    ; sardTarget =
        Sard.canonicalSardRegularValueSlicingTarget
    ; sardTargetIsCanonical =
        refl
    ; regularValueCarrier =
        Sard.canonicalRegularValueCarrier
    ; regularValueCarrierIsCanonical =
        refl
    ; sardExceptionalSet =
        Sard.canonicalSardExceptionalSetCarrier
    ; sardExceptionalSetIsCanonical =
        refl
    ; stripSlicingEstimate =
        Sard.canonicalStripSlicingEstimateCarrier
    ; stripSlicingEstimateIsCanonical =
        refl
    ; antipodalTube =
        Antipodal.canonicalAntipodalTubeCarrier
    ; antipodalTubeIsCanonical =
        refl
    ; antipodalNullMassTarget =
        Antipodal.canonicalAntipodalTubeNullMassTarget
    ; antipodalNullMassTargetIsCanonical =
        refl
    ; normalizeSumDomain =
        Antipodal.canonicalNormalizeSumDomainExclusion
    ; normalizeSumDomainIsCanonical =
        refl
    ; uniformNormalTarget =
        UniformNormal.canonicalUniformInNormalConstantsTarget
    ; uniformNormalTargetIsCanonical =
        refl
    ; cA4LowerBound =
        UniformNormal.canonicalLowerBoundConstantCA4Carrier
    ; cA4LowerBoundIsCanonical =
        refl
    ; etaScaleSeparation =
        UniformNormal.canonicalEtaWindowScaleSeparationCarrier
    ; etaScaleSeparationIsCanonical =
        refl
    ; uniformCoareaObligation =
        UniformNormal.canonicalUniformInNormalCoareaConstantObligationCarrier
    ; uniformCoareaObligationIsCanonical =
        refl
    ; outputPreimageStillFalse =
        refl
    ; sardStillFalse =
        refl
    ; antipodalStillFalse =
        refl
    ; uniformNormalStillFalse =
        refl
    ; cA4StillFalse =
        refl
    }

------------------------------------------------------------------------
-- Slab estimate carriers.

data EtaParameterCarrier : Set where
  positiveEtaWidthForGreatCircleStrip :
    Nat →
    OutputPreimage.OutputGreatCircleStripTestCarrier →
    EtaParameterCarrier

data CoareaSlabDomainCarrier : Set where
  etaStripSlabInNormalizeSumPreimageDomain :
    EtaParameterCarrier →
    OutputPreimage.PhiNormalizeSumPreimageCarrier →
    OutputPreimage.PreimageMeasureDomainCarrier →
    Antipodal.NormalizeSumDomainExclusion →
    CoareaSlabDomainCarrier

data RegularCoareaSliceLedgerCarrier : Set where
  regularValuesAndSardExceptionalSlicesSeparated :
    CoareaSlabDomainCarrier →
    Sard.RegularValueCarrier →
    Sard.SardExceptionalSetCarrier →
    Sard.StripSlicingEstimateCarrier →
    RegularCoareaSliceLedgerCarrier

data UniformEtaSlabPositiveTermCarrier : Set where
  cA4TimesEtaPositiveMassScaleUniformInNormal :
    EtaParameterCarrier →
    UniformNormal.LowerBoundConstantCA4Carrier →
    UniformNormal.UniformInNormalCoareaConstantObligationCarrier →
    UniformEtaSlabPositiveTermCarrier

data EtaSlabErrorTermCarrier : Set where
  antipodalTubeError :
    Antipodal.AntipodalTubeNullMassTarget →
    EtaSlabErrorTermCarrier
  sardCriticalValueError :
    Sard.SardExceptionalSetCarrier →
    EtaSlabErrorTermCarrier
  outputPreimageNullExceptionalError :
    OutputPreimage.NullExceptionalBudgetCarrier →
    EtaSlabErrorTermCarrier
  etaScaleSeparationError :
    UniformNormal.EtaWindowScaleSeparationCarrier →
    EtaSlabErrorTermCarrier

data QuantifiedEtaSlabErrorBudgetCarrier : Set where
  sumOfExceptionalErrorsIsRecordedBelowHalfCA4Eta :
    UniformEtaSlabPositiveTermCarrier →
    List EtaSlabErrorTermCarrier →
    OutputPreimage.NullExceptionalBudgetCarrier →
    Antipodal.AntipodalTubeCarrier →
    QuantifiedEtaSlabErrorBudgetCarrier

data EtaStripCoareaSlabEstimateCarrier : Set where
  etaStripPreimageHasPositiveCoareaMassAfterErrors :
    RegularCoareaSliceLedgerCarrier →
    UniformEtaSlabPositiveTermCarrier →
    QuantifiedEtaSlabErrorBudgetCarrier →
    OutputPreimage.StripWidthJacobianBudgetCarrier →
    OutputPreimage.OutputStripPreimageMeasureEstimateCarrier →
    EtaStripCoareaSlabEstimateCarrier

data EtaSlabRouteToOutputPreimageCarrier : Set where
  etaSlabEstimateFeedsOutputStripPreimageConsumerFailClosed :
    EtaStripCoareaSlabEstimateCarrier →
    OutputPreimage.A4OutputStripPreimageEstimateConsumer →
    OutputPreimage.OutputStripPreimageMeasureEstimateTarget →
    UniformNormal.UniformNormalConstantRouteToErrorBudgetCarrier →
    EtaSlabRouteToOutputPreimageCarrier

data EtaStripCoareaSlabEstimateTarget : Set where
  quantifiedEtaStripCoareaSlabEstimateRecordedFailClosed :
    ImportedEtaStripCoareaSlabSupport →
    EtaParameterCarrier →
    CoareaSlabDomainCarrier →
    RegularCoareaSliceLedgerCarrier →
    UniformEtaSlabPositiveTermCarrier →
    QuantifiedEtaSlabErrorBudgetCarrier →
    EtaStripCoareaSlabEstimateCarrier →
    EtaSlabRouteToOutputPreimageCarrier →
    EtaStripCoareaSlabEstimateTarget

canonicalEtaParameterCarrier :
  EtaParameterCarrier
canonicalEtaParameterCarrier =
  positiveEtaWidthForGreatCircleStrip
    (suc zero)
    OutputPreimage.canonicalOutputGreatCircleStripTestCarrier

canonicalCoareaSlabDomainCarrier :
  CoareaSlabDomainCarrier
canonicalCoareaSlabDomainCarrier =
  etaStripSlabInNormalizeSumPreimageDomain
    canonicalEtaParameterCarrier
    OutputPreimage.canonicalPhiNormalizeSumPreimageCarrier
    OutputPreimage.canonicalPreimageMeasureDomainCarrier
    Antipodal.canonicalNormalizeSumDomainExclusion

canonicalRegularCoareaSliceLedgerCarrier :
  RegularCoareaSliceLedgerCarrier
canonicalRegularCoareaSliceLedgerCarrier =
  regularValuesAndSardExceptionalSlicesSeparated
    canonicalCoareaSlabDomainCarrier
    Sard.canonicalRegularValueCarrier
    Sard.canonicalSardExceptionalSetCarrier
    Sard.canonicalStripSlicingEstimateCarrier

canonicalUniformEtaSlabPositiveTermCarrier :
  UniformEtaSlabPositiveTermCarrier
canonicalUniformEtaSlabPositiveTermCarrier =
  cA4TimesEtaPositiveMassScaleUniformInNormal
    canonicalEtaParameterCarrier
    UniformNormal.canonicalLowerBoundConstantCA4Carrier
    UniformNormal.canonicalUniformInNormalCoareaConstantObligationCarrier

canonicalAntipodalEtaSlabErrorTermCarrier :
  EtaSlabErrorTermCarrier
canonicalAntipodalEtaSlabErrorTermCarrier =
  antipodalTubeError
    Antipodal.canonicalAntipodalTubeNullMassTarget

canonicalSardEtaSlabErrorTermCarrier :
  EtaSlabErrorTermCarrier
canonicalSardEtaSlabErrorTermCarrier =
  sardCriticalValueError
    Sard.canonicalSardExceptionalSetCarrier

canonicalNullExceptionalEtaSlabErrorTermCarrier :
  EtaSlabErrorTermCarrier
canonicalNullExceptionalEtaSlabErrorTermCarrier =
  outputPreimageNullExceptionalError
    OutputPreimage.canonicalNullExceptionalBudgetCarrier

canonicalEtaScaleSeparationErrorTermCarrier :
  EtaSlabErrorTermCarrier
canonicalEtaScaleSeparationErrorTermCarrier =
  etaScaleSeparationError
    UniformNormal.canonicalEtaWindowScaleSeparationCarrier

canonicalEtaSlabErrorTerms :
  List EtaSlabErrorTermCarrier
canonicalEtaSlabErrorTerms =
  canonicalAntipodalEtaSlabErrorTermCarrier
  ∷ canonicalSardEtaSlabErrorTermCarrier
  ∷ canonicalNullExceptionalEtaSlabErrorTermCarrier
  ∷ canonicalEtaScaleSeparationErrorTermCarrier
  ∷ []

etaSlabErrorTermCount : Nat
etaSlabErrorTermCount =
  listLength canonicalEtaSlabErrorTerms

etaSlabErrorTermCountIs4 :
  etaSlabErrorTermCount ≡ 4
etaSlabErrorTermCountIs4 =
  refl

canonicalQuantifiedEtaSlabErrorBudgetCarrier :
  QuantifiedEtaSlabErrorBudgetCarrier
canonicalQuantifiedEtaSlabErrorBudgetCarrier =
  sumOfExceptionalErrorsIsRecordedBelowHalfCA4Eta
    canonicalUniformEtaSlabPositiveTermCarrier
    canonicalEtaSlabErrorTerms
    OutputPreimage.canonicalNullExceptionalBudgetCarrier
    Antipodal.canonicalAntipodalTubeCarrier

canonicalEtaStripCoareaSlabEstimateCarrier :
  EtaStripCoareaSlabEstimateCarrier
canonicalEtaStripCoareaSlabEstimateCarrier =
  etaStripPreimageHasPositiveCoareaMassAfterErrors
    canonicalRegularCoareaSliceLedgerCarrier
    canonicalUniformEtaSlabPositiveTermCarrier
    canonicalQuantifiedEtaSlabErrorBudgetCarrier
    OutputPreimage.canonicalStripWidthJacobianBudgetCarrier
    OutputPreimage.canonicalOutputStripPreimageMeasureEstimateCarrier

canonicalEtaSlabRouteToOutputPreimageCarrier :
  EtaSlabRouteToOutputPreimageCarrier
canonicalEtaSlabRouteToOutputPreimageCarrier =
  etaSlabEstimateFeedsOutputStripPreimageConsumerFailClosed
    canonicalEtaStripCoareaSlabEstimateCarrier
    OutputPreimage.canonicalA4OutputStripPreimageEstimateConsumer
    OutputPreimage.canonicalOutputStripPreimageMeasureEstimateTarget
    UniformNormal.canonicalUniformNormalConstantRouteToErrorBudgetCarrier

canonicalEtaStripCoareaSlabEstimateTarget :
  EtaStripCoareaSlabEstimateTarget
canonicalEtaStripCoareaSlabEstimateTarget =
  quantifiedEtaStripCoareaSlabEstimateRecordedFailClosed
    canonicalImportedEtaStripCoareaSlabSupport
    canonicalEtaParameterCarrier
    canonicalCoareaSlabDomainCarrier
    canonicalRegularCoareaSliceLedgerCarrier
    canonicalUniformEtaSlabPositiveTermCarrier
    canonicalQuantifiedEtaSlabErrorBudgetCarrier
    canonicalEtaStripCoareaSlabEstimateCarrier
    canonicalEtaSlabRouteToOutputPreimageCarrier

------------------------------------------------------------------------
-- Obligations, blockers, and status rows.

data EtaStripCoareaSlabObligation : Set where
  consumeOutputStripPreimageMeasureEstimateBoundary :
    EtaStripCoareaSlabObligation
  consumeSardRegularValueSlicingBoundary :
    EtaStripCoareaSlabObligation
  consumeAntipodalTubeNullMassBoundary :
    EtaStripCoareaSlabObligation
  consumeUniformInNormalConstantsBoundary :
    EtaStripCoareaSlabObligation
  quantifyEtaAndGreatCircleNormal :
    EtaStripCoareaSlabObligation
  restrictSlabToNormalizeSumTubeComplement :
    EtaStripCoareaSlabObligation
  sliceRegularValuesAndDiscardSardCriticalValues :
    EtaStripCoareaSlabObligation
  insertUniformPositiveTermCA4TimesEta :
    EtaStripCoareaSlabObligation
  subtractAntipodalCriticalPacketAndScaleErrors :
    EtaStripCoareaSlabObligation
  proveResidualPositiveAfterErrors :
    EtaStripCoareaSlabObligation
  routeEstimateToOutputStripPreimageConsumer :
    EtaStripCoareaSlabObligation
  keepA4A6NSClayAndTerminalPromotionsFalse :
    EtaStripCoareaSlabObligation

canonicalEtaStripCoareaSlabObligations :
  List EtaStripCoareaSlabObligation
canonicalEtaStripCoareaSlabObligations =
  consumeOutputStripPreimageMeasureEstimateBoundary
  ∷ consumeSardRegularValueSlicingBoundary
  ∷ consumeAntipodalTubeNullMassBoundary
  ∷ consumeUniformInNormalConstantsBoundary
  ∷ quantifyEtaAndGreatCircleNormal
  ∷ restrictSlabToNormalizeSumTubeComplement
  ∷ sliceRegularValuesAndDiscardSardCriticalValues
  ∷ insertUniformPositiveTermCA4TimesEta
  ∷ subtractAntipodalCriticalPacketAndScaleErrors
  ∷ proveResidualPositiveAfterErrors
  ∷ routeEstimateToOutputStripPreimageConsumer
  ∷ keepA4A6NSClayAndTerminalPromotionsFalse
  ∷ []

etaStripCoareaSlabObligationCount : Nat
etaStripCoareaSlabObligationCount =
  listLength canonicalEtaStripCoareaSlabObligations

etaStripCoareaSlabObligationCountIs12 :
  etaStripCoareaSlabObligationCount ≡ 12
etaStripCoareaSlabObligationCountIs12 =
  refl

data EtaStripCoareaSlabBlocker : Set where
  missingEtaPositiveWidthQuantification :
    EtaStripCoareaSlabBlocker
  missingRegularCoareaSliceProof :
    EtaStripCoareaSlabBlocker
  missingSardCriticalValueNullRouting :
    EtaStripCoareaSlabBlocker
  missingAntipodalTubeErrorEstimate :
    EtaStripCoareaSlabBlocker
  missingUniformCA4LowerBoundProof :
    EtaStripCoareaSlabBlocker
  missingErrorBelowHalfCA4EtaProof :
    EtaStripCoareaSlabBlocker
  missingOutputPreimageMeasurePromotion :
    EtaStripCoareaSlabBlocker
  missingA4Promotion :
    EtaStripCoareaSlabBlocker
  missingA6Promotion :
    EtaStripCoareaSlabBlocker
  missingNSClayPromotion :
    EtaStripCoareaSlabBlocker

canonicalEtaStripCoareaSlabBlockers :
  List EtaStripCoareaSlabBlocker
canonicalEtaStripCoareaSlabBlockers =
  missingEtaPositiveWidthQuantification
  ∷ missingRegularCoareaSliceProof
  ∷ missingSardCriticalValueNullRouting
  ∷ missingAntipodalTubeErrorEstimate
  ∷ missingUniformCA4LowerBoundProof
  ∷ missingErrorBelowHalfCA4EtaProof
  ∷ missingOutputPreimageMeasurePromotion
  ∷ missingA4Promotion
  ∷ missingA6Promotion
  ∷ missingNSClayPromotion
  ∷ []

etaStripCoareaSlabBlockerCount : Nat
etaStripCoareaSlabBlockerCount =
  listLength canonicalEtaStripCoareaSlabBlockers

etaStripCoareaSlabBlockerCountIs10 :
  etaStripCoareaSlabBlockerCount ≡ 10
etaStripCoareaSlabBlockerCountIs10 =
  refl

data EtaStripCoareaSlabStatusRow : Set where
  boundaryRecordedStatus :
    EtaStripCoareaSlabStatusRow
  fourRequestedInputBoundariesConsumedStatus :
    EtaStripCoareaSlabStatusRow
  etaParameterAndSlabDomainRecordedStatus :
    EtaStripCoareaSlabStatusRow
  regularSardSliceLedgerRecordedStatus :
    EtaStripCoareaSlabStatusRow
  cA4TimesEtaPositiveTermRecordedStatus :
    EtaStripCoareaSlabStatusRow
  quantifiedErrorBudgetRecordedStatus :
    EtaStripCoareaSlabStatusRow
  outputPreimageRouteRecordedStatus :
    EtaStripCoareaSlabStatusRow
  theoremAndPromotionFlagsRemainFalseStatus :
    EtaStripCoareaSlabStatusRow

canonicalEtaStripCoareaSlabStatusRows :
  List EtaStripCoareaSlabStatusRow
canonicalEtaStripCoareaSlabStatusRows =
  boundaryRecordedStatus
  ∷ fourRequestedInputBoundariesConsumedStatus
  ∷ etaParameterAndSlabDomainRecordedStatus
  ∷ regularSardSliceLedgerRecordedStatus
  ∷ cA4TimesEtaPositiveTermRecordedStatus
  ∷ quantifiedErrorBudgetRecordedStatus
  ∷ outputPreimageRouteRecordedStatus
  ∷ theoremAndPromotionFlagsRemainFalseStatus
  ∷ []

etaStripCoareaSlabStatusRowCount : Nat
etaStripCoareaSlabStatusRowCount =
  listLength canonicalEtaStripCoareaSlabStatusRows

etaStripCoareaSlabStatusRowCountIs8 :
  etaStripCoareaSlabStatusRowCount ≡ 8
etaStripCoareaSlabStatusRowCountIs8 =
  refl

------------------------------------------------------------------------
-- Promotion-closed type.

data EtaStripCoareaSlabPromotion : Set where

etaStripCoareaSlabPromotionImpossibleHere :
  EtaStripCoareaSlabPromotion →
  ⊥
etaStripCoareaSlabPromotionImpossibleHere ()

------------------------------------------------------------------------
-- Fail-closed governance flags.

NSA4EtaStripCoareaSlabEstimateBoundaryRecorded : Bool
NSA4EtaStripCoareaSlabEstimateBoundaryRecorded =
  true

etaParameterRecorded : Bool
etaParameterRecorded =
  true

coareaSlabDomainRecorded : Bool
coareaSlabDomainRecorded =
  true

regularCoareaSliceLedgerRecorded : Bool
regularCoareaSliceLedgerRecorded =
  true

uniformPositiveTermCA4EtaRecorded : Bool
uniformPositiveTermCA4EtaRecorded =
  true

quantifiedEtaSlabErrorBudgetRecorded : Bool
quantifiedEtaSlabErrorBudgetRecorded =
  true

etaSlabRouteToOutputPreimageRecorded : Bool
etaSlabRouteToOutputPreimageRecorded =
  true

etaPositiveWidthQuantificationProved : Bool
etaPositiveWidthQuantificationProved =
  false

regularCoareaSliceProofCompleted : Bool
regularCoareaSliceProofCompleted =
  false

SardCriticalValueRoutingProved : Bool
SardCriticalValueRoutingProved =
  false

antipodalErrorEstimateProved : Bool
antipodalErrorEstimateProved =
  false

uniformCA4LowerBoundProved : Bool
uniformCA4LowerBoundProved =
  false

errorBelowHalfCA4EtaProved : Bool
errorBelowHalfCA4EtaProved =
  false

etaStripCoareaSlabEstimateProved : Bool
etaStripCoareaSlabEstimateProved =
  false

outputStripPreimageMeasureEstimatePromoted : Bool
outputStripPreimageMeasureEstimatePromoted =
  false

A4TheoremPromoted : Bool
A4TheoremPromoted =
  false

A6TheoremPromoted : Bool
A6TheoremPromoted =
  false

fullLocalDefectMonotonicity : Bool
fullLocalDefectMonotonicity =
  false

fullClayNSSolved : Bool
fullClayNSSolved =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

recordsBoundary :
  NSA4EtaStripCoareaSlabEstimateBoundaryRecorded ≡ true
recordsBoundary =
  refl

recordsEtaParameter :
  etaParameterRecorded ≡ true
recordsEtaParameter =
  refl

recordsCoareaSlabDomain :
  coareaSlabDomainRecorded ≡ true
recordsCoareaSlabDomain =
  refl

recordsRegularCoareaSliceLedger :
  regularCoareaSliceLedgerRecorded ≡ true
recordsRegularCoareaSliceLedger =
  refl

recordsUniformPositiveTermCA4Eta :
  uniformPositiveTermCA4EtaRecorded ≡ true
recordsUniformPositiveTermCA4Eta =
  refl

recordsQuantifiedEtaSlabErrorBudget :
  quantifiedEtaSlabErrorBudgetRecorded ≡ true
recordsQuantifiedEtaSlabErrorBudget =
  refl

recordsEtaSlabRouteToOutputPreimage :
  etaSlabRouteToOutputPreimageRecorded ≡ true
recordsEtaSlabRouteToOutputPreimage =
  refl

keepsEtaPositiveWidthQuantificationFalse :
  etaPositiveWidthQuantificationProved ≡ false
keepsEtaPositiveWidthQuantificationFalse =
  refl

keepsRegularCoareaSliceProofFalse :
  regularCoareaSliceProofCompleted ≡ false
keepsRegularCoareaSliceProofFalse =
  refl

keepsSardCriticalValueRoutingFalse :
  SardCriticalValueRoutingProved ≡ false
keepsSardCriticalValueRoutingFalse =
  refl

keepsAntipodalErrorEstimateFalse :
  antipodalErrorEstimateProved ≡ false
keepsAntipodalErrorEstimateFalse =
  refl

keepsUniformCA4LowerBoundFalse :
  uniformCA4LowerBoundProved ≡ false
keepsUniformCA4LowerBoundFalse =
  refl

keepsErrorBelowHalfCA4EtaFalse :
  errorBelowHalfCA4EtaProved ≡ false
keepsErrorBelowHalfCA4EtaFalse =
  refl

keepsEtaStripCoareaSlabEstimateFalse :
  etaStripCoareaSlabEstimateProved ≡ false
keepsEtaStripCoareaSlabEstimateFalse =
  refl

keepsOutputStripPreimageMeasureEstimatePromotedFalse :
  outputStripPreimageMeasureEstimatePromoted ≡ false
keepsOutputStripPreimageMeasureEstimatePromotedFalse =
  refl

keepsA4TheoremPromotedFalse :
  A4TheoremPromoted ≡ false
keepsA4TheoremPromotedFalse =
  refl

keepsA6TheoremPromotedFalse :
  A6TheoremPromoted ≡ false
keepsA6TheoremPromotedFalse =
  refl

keepsFullLocalDefectMonotonicityFalse :
  fullLocalDefectMonotonicity ≡ false
keepsFullLocalDefectMonotonicityFalse =
  refl

keepsFullClayNSSolvedFalse :
  fullClayNSSolved ≡ false
keepsFullClayNSSolvedFalse =
  refl

keepsClayPromotionFalse :
  clayNavierStokesPromoted ≡ false
keepsClayPromotionFalse =
  refl

keepsTerminalPromotionFalse :
  terminalPromotion ≡ false
keepsTerminalPromotionFalse =
  refl

------------------------------------------------------------------------
-- O/R/C/S/L/P/G/F.

organizationString : String
organizationString =
  "O: Worker-2 boundary isolates the eta-strip coarea slab estimate in NS A4 without editing parent docs or aggregate imports."

requirementString : String
requirementString =
  "R: Compose output-strip preimage, Sard regular-value slicing, antipodal tube null-mass, and uniform-in-normal constants into a quantified c_A4*eta-minus-errors slab ledger."

codeArtifactString : String
codeArtifactString =
  "C: DASHI.Physics.Closure.NSA4EtaStripCoareaSlabEstimateBoundary exports imported support, eta/slab carriers, positivity and error-budget carriers, target, blockers, status rows, and fail-closed flags."

stateString : String
stateString =
  "S: Boundary records the proof shape only; eta positivity, regular coarea slicing, Sard routing, antipodal error, c_A4 positivity, residual positivity, A4, A6, NS Clay, and terminal promotion remain false."

latticeString : String
latticeString =
  "L: eta strip -> non-antipodal Phi preimage slab -> regular Sard slices -> c_A4*eta positive term -> exceptional-error subtraction -> output-preimage route."

proposalString : String
proposalString =
  "P: Promote only after proving the regular coarea slice estimate and the quantified error inequality errors <= (c_A4*eta)/2 using the imported child surfaces."

governanceString : String
governanceString =
  "G: Recording flags are true; all theorem and promotion flags are false by refl, preserving fail-closed Clay governance."

gapString : String
gapString =
  "F: Remaining gaps are eta-width quantification, Sard/regular coarea slicing, antipodal and exceptional error estimates, uniform c_A4 lower bound, residual positivity, output-preimage promotion, A4/A6, and NS Clay."

------------------------------------------------------------------------
-- Canonical receipt.

record NSA4EtaStripCoareaSlabEstimateBoundary : Set where
  field
    O-organization :
      String
    R-requirement :
      String
    C-artifact :
      String
    S-state :
      String
    L-lattice :
      String
    P-proposal :
      String
    G-governance :
      String
    F-gap :
      String
    importedSupport :
      ImportedEtaStripCoareaSlabSupport
    etaParameter :
      EtaParameterCarrier
    slabDomain :
      CoareaSlabDomainCarrier
    regularSliceLedger :
      RegularCoareaSliceLedgerCarrier
    positiveTerm :
      UniformEtaSlabPositiveTermCarrier
    errorTerms :
      List EtaSlabErrorTermCarrier
    errorTermCountIs4 :
      etaSlabErrorTermCount ≡ 4
    errorBudget :
      QuantifiedEtaSlabErrorBudgetCarrier
    estimateCarrier :
      EtaStripCoareaSlabEstimateCarrier
    routeToOutputPreimage :
      EtaSlabRouteToOutputPreimageCarrier
    target :
      EtaStripCoareaSlabEstimateTarget
    obligations :
      List EtaStripCoareaSlabObligation
    obligationCountIs12 :
      etaStripCoareaSlabObligationCount ≡ 12
    blockers :
      List EtaStripCoareaSlabBlocker
    blockerCountIs10 :
      etaStripCoareaSlabBlockerCount ≡ 10
    statusRows :
      List EtaStripCoareaSlabStatusRow
    statusRowCountIs8 :
      etaStripCoareaSlabStatusRowCount ≡ 8
    boundaryRecordedTrue :
      NSA4EtaStripCoareaSlabEstimateBoundaryRecorded ≡ true
    etaParameterRecordedTrue :
      etaParameterRecorded ≡ true
    coareaSlabDomainRecordedTrue :
      coareaSlabDomainRecorded ≡ true
    regularCoareaSliceLedgerRecordedTrue :
      regularCoareaSliceLedgerRecorded ≡ true
    positiveTermRecordedTrue :
      uniformPositiveTermCA4EtaRecorded ≡ true
    errorBudgetRecordedTrue :
      quantifiedEtaSlabErrorBudgetRecorded ≡ true
    routeRecordedTrue :
      etaSlabRouteToOutputPreimageRecorded ≡ true
    etaPositiveWidthStillFalse :
      etaPositiveWidthQuantificationProved ≡ false
    regularCoareaSliceStillFalse :
      regularCoareaSliceProofCompleted ≡ false
    SardCriticalRoutingStillFalse :
      SardCriticalValueRoutingProved ≡ false
    antipodalErrorStillFalse :
      antipodalErrorEstimateProved ≡ false
    uniformCA4StillFalse :
      uniformCA4LowerBoundProved ≡ false
    errorBelowHalfStillFalse :
      errorBelowHalfCA4EtaProved ≡ false
    slabEstimateStillFalse :
      etaStripCoareaSlabEstimateProved ≡ false
    outputPreimagePromotionStillFalse :
      outputStripPreimageMeasureEstimatePromoted ≡ false
    A4PromotionStillFalse :
      A4TheoremPromoted ≡ false
    A6PromotionStillFalse :
      A6TheoremPromoted ≡ false
    claySolvedStillFalse :
      fullClayNSSolved ≡ false
    clayPromotionStillFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionStillFalse :
      terminalPromotion ≡ false

canonicalNSA4EtaStripCoareaSlabEstimateBoundary :
  NSA4EtaStripCoareaSlabEstimateBoundary
canonicalNSA4EtaStripCoareaSlabEstimateBoundary =
  record
    { O-organization =
        organizationString
    ; R-requirement =
        requirementString
    ; C-artifact =
        codeArtifactString
    ; S-state =
        stateString
    ; L-lattice =
        latticeString
    ; P-proposal =
        proposalString
    ; G-governance =
        governanceString
    ; F-gap =
        gapString
    ; importedSupport =
        canonicalImportedEtaStripCoareaSlabSupport
    ; etaParameter =
        canonicalEtaParameterCarrier
    ; slabDomain =
        canonicalCoareaSlabDomainCarrier
    ; regularSliceLedger =
        canonicalRegularCoareaSliceLedgerCarrier
    ; positiveTerm =
        canonicalUniformEtaSlabPositiveTermCarrier
    ; errorTerms =
        canonicalEtaSlabErrorTerms
    ; errorTermCountIs4 =
        etaSlabErrorTermCountIs4
    ; errorBudget =
        canonicalQuantifiedEtaSlabErrorBudgetCarrier
    ; estimateCarrier =
        canonicalEtaStripCoareaSlabEstimateCarrier
    ; routeToOutputPreimage =
        canonicalEtaSlabRouteToOutputPreimageCarrier
    ; target =
        canonicalEtaStripCoareaSlabEstimateTarget
    ; obligations =
        canonicalEtaStripCoareaSlabObligations
    ; obligationCountIs12 =
        etaStripCoareaSlabObligationCountIs12
    ; blockers =
        canonicalEtaStripCoareaSlabBlockers
    ; blockerCountIs10 =
        etaStripCoareaSlabBlockerCountIs10
    ; statusRows =
        canonicalEtaStripCoareaSlabStatusRows
    ; statusRowCountIs8 =
        etaStripCoareaSlabStatusRowCountIs8
    ; boundaryRecordedTrue =
        recordsBoundary
    ; etaParameterRecordedTrue =
        recordsEtaParameter
    ; coareaSlabDomainRecordedTrue =
        recordsCoareaSlabDomain
    ; regularCoareaSliceLedgerRecordedTrue =
        recordsRegularCoareaSliceLedger
    ; positiveTermRecordedTrue =
        recordsUniformPositiveTermCA4Eta
    ; errorBudgetRecordedTrue =
        recordsQuantifiedEtaSlabErrorBudget
    ; routeRecordedTrue =
        recordsEtaSlabRouteToOutputPreimage
    ; etaPositiveWidthStillFalse =
        keepsEtaPositiveWidthQuantificationFalse
    ; regularCoareaSliceStillFalse =
        keepsRegularCoareaSliceProofFalse
    ; SardCriticalRoutingStillFalse =
        keepsSardCriticalValueRoutingFalse
    ; antipodalErrorStillFalse =
        keepsAntipodalErrorEstimateFalse
    ; uniformCA4StillFalse =
        keepsUniformCA4LowerBoundFalse
    ; errorBelowHalfStillFalse =
        keepsErrorBelowHalfCA4EtaFalse
    ; slabEstimateStillFalse =
        keepsEtaStripCoareaSlabEstimateFalse
    ; outputPreimagePromotionStillFalse =
        keepsOutputStripPreimageMeasureEstimatePromotedFalse
    ; A4PromotionStillFalse =
        keepsA4TheoremPromotedFalse
    ; A6PromotionStillFalse =
        keepsA6TheoremPromotedFalse
    ; claySolvedStillFalse =
        keepsFullClayNSSolvedFalse
    ; clayPromotionStillFalse =
        keepsClayPromotionFalse
    ; terminalPromotionStillFalse =
        keepsTerminalPromotionFalse
    }
