module DASHI.Physics.Closure.NSTransferOperatorBiasNeutralityBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSBiotSavartStrainMeanSquareExactFormulaBoundary
  as MeanSquare
import DASHI.Physics.Closure.NSCascadeKappaArcsineLawBoundary
  as Arcsine

------------------------------------------------------------------------
-- NS-F7 transfer-operator bias neutrality boundary.
--
-- Fail-closed receipt for the finite-statistical transfer-operator claim:
--
--   If the transfer output has the corrected arcsine kappa law and the
--   transfer weights make lambda independent of kappa at residual scale r,
--   then the transfer-operator bias obeys the RMS consequence
--
--     |Bias(mu_r)| <= delta_r * sqrt(11/60).
--
-- The conditional is finite-statistical only.  This module records no
-- unconditional Type-I kappa-bias theorem, no PDE transfer theorem, no
-- Navier-Stokes Clay theorem, and no terminal promotion.

data List (A : Set) : Set where
  [] :
    List A
  _∷_ :
    A →
    List A →
    List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

data ⊥ : Set where

------------------------------------------------------------------------
-- Imported finite anchors.

arcsineBoundaryReference : String
arcsineBoundaryReference =
  "DASHI.Physics.Closure.NSCascadeKappaArcsineLawBoundary"

meanSquareBoundaryReference : String
meanSquareBoundaryReference =
  "DASHI.Physics.Closure.NSBiotSavartStrainMeanSquareExactFormulaBoundary"

arcsineBoundaryImported : Bool
arcsineBoundaryImported =
  true

meanSquareBoundaryImported : Bool
meanSquareBoundaryImported =
  true

record ImportedNSF7FiniteStatisticalSupport : Set where
  field
    arcsineBoundary :
      Arcsine.NSCascadeKappaArcsineLawBoundary
    arcsineBoundaryIsCanonical :
      arcsineBoundary ≡ Arcsine.canonicalNSCascadeKappaArcsineLawBoundary
    meanSquareBoundary :
      MeanSquare.NSBiotSavartStrainMeanSquareExactFormulaBoundary
    meanSquareBoundaryIsCanonical :
      meanSquareBoundary
        ≡ MeanSquare.canonicalNSBiotSavartStrainMeanSquareExactFormulaBoundary
    arcsineBoundaryImportedIsTrue :
      arcsineBoundaryImported ≡ true
    meanSquareBoundaryImportedIsTrue :
      meanSquareBoundaryImported ≡ true

canonicalImportedNSF7FiniteStatisticalSupport :
  ImportedNSF7FiniteStatisticalSupport
canonicalImportedNSF7FiniteStatisticalSupport =
  record
    { arcsineBoundary =
        Arcsine.canonicalNSCascadeKappaArcsineLawBoundary
    ; arcsineBoundaryIsCanonical =
        refl
    ; meanSquareBoundary =
        MeanSquare.canonicalNSBiotSavartStrainMeanSquareExactFormulaBoundary
    ; meanSquareBoundaryIsCanonical =
        refl
    ; arcsineBoundaryImportedIsTrue =
        refl
    ; meanSquareBoundaryImportedIsTrue =
        refl
    }

------------------------------------------------------------------------
-- Conditional finite-statistical claim.

data TransferOperatorBiasNeutralityPremise : Set where
  nsF7TransferOperatorOutputMeasureMuR :
    TransferOperatorBiasNeutralityPremise
  residualScaleDeltaR :
    TransferOperatorBiasNeutralityPremise
  kappaOutputHasCorrectedArcsineLaw :
    TransferOperatorBiasNeutralityPremise
  lambdaKappaIndependenceAtScaleR :
    TransferOperatorBiasNeutralityPremise
  lambdaSquareRmsCoefficientElevenSixtieth :
    TransferOperatorBiasNeutralityPremise
  noUnconditionalFiniteBiasClaim :
    TransferOperatorBiasNeutralityPremise

canonicalTransferOperatorBiasNeutralityPremises :
  List TransferOperatorBiasNeutralityPremise
canonicalTransferOperatorBiasNeutralityPremises =
  nsF7TransferOperatorOutputMeasureMuR
  ∷ residualScaleDeltaR
  ∷ kappaOutputHasCorrectedArcsineLaw
  ∷ lambdaKappaIndependenceAtScaleR
  ∷ lambdaSquareRmsCoefficientElevenSixtieth
  ∷ noUnconditionalFiniteBiasClaim
  ∷ []

transferOperatorBiasNeutralityPremiseCount : Nat
transferOperatorBiasNeutralityPremiseCount =
  listLength canonicalTransferOperatorBiasNeutralityPremises

transferOperatorBiasNeutralityPremiseCountIs6 :
  transferOperatorBiasNeutralityPremiseCount ≡ 6
transferOperatorBiasNeutralityPremiseCountIs6 =
  refl

data TransferOperatorBiasNeutralityConditional : Set where
  conditionalOnArcsineOutputAndLambdaKappaIndependence :
    TransferOperatorBiasNeutralityConditional
  finiteStatisticalOnlyNotPdeMeasureConstruction :
    TransferOperatorBiasNeutralityConditional
  independenceHypothesisNotDerivedHere :
    TransferOperatorBiasNeutralityConditional
  arcsineOutputHypothesisImportedNotReprovedHere :
    TransferOperatorBiasNeutralityConditional
  noTypeIBlowupMeasureClosure :
    TransferOperatorBiasNeutralityConditional

canonicalTransferOperatorBiasNeutralityConditionals :
  List TransferOperatorBiasNeutralityConditional
canonicalTransferOperatorBiasNeutralityConditionals =
  conditionalOnArcsineOutputAndLambdaKappaIndependence
  ∷ finiteStatisticalOnlyNotPdeMeasureConstruction
  ∷ independenceHypothesisNotDerivedHere
  ∷ arcsineOutputHypothesisImportedNotReprovedHere
  ∷ noTypeIBlowupMeasureClosure
  ∷ []

transferOperatorBiasNeutralityConditionalCount : Nat
transferOperatorBiasNeutralityConditionalCount =
  listLength canonicalTransferOperatorBiasNeutralityConditionals

transferOperatorBiasNeutralityConditionalCountIs5 :
  transferOperatorBiasNeutralityConditionalCount ≡ 5
transferOperatorBiasNeutralityConditionalCountIs5 =
  refl

data TransferOperatorBiasNeutralityConsequence : Set where
  biasMuRAbsoluteValueBoundedByDeltaRTimesRmsLambda :
    TransferOperatorBiasNeutralityConsequence
  rmsLambdaRecordedAsSqrtElevenSixtieth :
    TransferOperatorBiasNeutralityConsequence
  displayedConsequenceIsAbsBiasMuRLeDeltaRSqrtElevenSixtieth :
    TransferOperatorBiasNeutralityConsequence
  consequenceDependsOnBothConditionalInputs :
    TransferOperatorBiasNeutralityConsequence
  noResidualDepletionOrCriticalRegularityConsequence :
    TransferOperatorBiasNeutralityConsequence

canonicalTransferOperatorBiasNeutralityConsequences :
  List TransferOperatorBiasNeutralityConsequence
canonicalTransferOperatorBiasNeutralityConsequences =
  biasMuRAbsoluteValueBoundedByDeltaRTimesRmsLambda
  ∷ rmsLambdaRecordedAsSqrtElevenSixtieth
  ∷ displayedConsequenceIsAbsBiasMuRLeDeltaRSqrtElevenSixtieth
  ∷ consequenceDependsOnBothConditionalInputs
  ∷ noResidualDepletionOrCriticalRegularityConsequence
  ∷ []

transferOperatorBiasNeutralityConsequenceCount : Nat
transferOperatorBiasNeutralityConsequenceCount =
  listLength canonicalTransferOperatorBiasNeutralityConsequences

transferOperatorBiasNeutralityConsequenceCountIs5 :
  transferOperatorBiasNeutralityConsequenceCount ≡ 5
transferOperatorBiasNeutralityConsequenceCountIs5 =
  refl

biasMuRConsequenceText : String
biasMuRConsequenceText =
  "|Bias(mu_r)| <= delta_r * sqrt(11/60)"

conditionalClaimText : String
conditionalClaimText =
  "Conditional on arcsine transfer output and lambda/kappa independence at scale r"

data TransferOperatorBiasNeutralityBlocker : Set where
  missingTransferOperatorArcsineOutputProof :
    TransferOperatorBiasNeutralityBlocker
  missingLambdaKappaIndependenceProof :
    TransferOperatorBiasNeutralityBlocker
  missingUnconditionalTypeIKappaBiasBound :
    TransferOperatorBiasNeutralityBlocker
  missingPdeTransferToActualNavierStokesMeasure :
    TransferOperatorBiasNeutralityBlocker
  missingResidualDepletionEstimate :
    TransferOperatorBiasNeutralityBlocker
  missingCriticalRegularityClosure :
    TransferOperatorBiasNeutralityBlocker

canonicalTransferOperatorBiasNeutralityBlockers :
  List TransferOperatorBiasNeutralityBlocker
canonicalTransferOperatorBiasNeutralityBlockers =
  missingTransferOperatorArcsineOutputProof
  ∷ missingLambdaKappaIndependenceProof
  ∷ missingUnconditionalTypeIKappaBiasBound
  ∷ missingPdeTransferToActualNavierStokesMeasure
  ∷ missingResidualDepletionEstimate
  ∷ missingCriticalRegularityClosure
  ∷ []

transferOperatorBiasNeutralityBlockerCount : Nat
transferOperatorBiasNeutralityBlockerCount =
  listLength canonicalTransferOperatorBiasNeutralityBlockers

transferOperatorBiasNeutralityBlockerCountIs6 :
  transferOperatorBiasNeutralityBlockerCount ≡ 6
transferOperatorBiasNeutralityBlockerCountIs6 =
  refl

------------------------------------------------------------------------
-- Fail-closed promotion guards.

data NSTransferOperatorBiasNeutralityPromotion : Set where

nsTransferOperatorBiasNeutralityPromotionImpossibleHere :
  NSTransferOperatorBiasNeutralityPromotion →
  ⊥
nsTransferOperatorBiasNeutralityPromotionImpossibleHere ()

finiteStatisticalClaimConditional : Bool
finiteStatisticalClaimConditional =
  true

arcsineOutputConditionDischargedHere : Bool
arcsineOutputConditionDischargedHere =
  false

lambdaKappaIndependenceProvedHere : Bool
lambdaKappaIndependenceProvedHere =
  false

typeIBiasBoundPromoted : Bool
typeIBiasBoundPromoted =
  false

pdeTransferPromoted : Bool
pdeTransferPromoted =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

data NSTransferOperatorBiasNeutralityStatus : Set where
  nsF7TransferOperatorBiasNeutralityRecorded_conditionalFinite_noPromotion :
    NSTransferOperatorBiasNeutralityStatus

nsTransferOperatorBiasNeutralitySummary : String
nsTransferOperatorBiasNeutralitySummary =
  "NS-F7 records a conditional finite-statistical receipt: if the transfer output is arcsine and lambda is independent of kappa at residual scale r, then |Bias(mu_r)| <= delta_r * sqrt(11/60).  The arcsine output and independence hypotheses are not discharged here; Type-I, PDE, Clay, and terminal promotion remain false."

record NSTransferOperatorBiasNeutralityBoundary : Set where
  field
    status :
      NSTransferOperatorBiasNeutralityStatus
    statusIsCanonical :
      status
        ≡ nsF7TransferOperatorBiasNeutralityRecorded_conditionalFinite_noPromotion
    finiteSupport :
      ImportedNSF7FiniteStatisticalSupport
    finiteSupportIsCanonical :
      finiteSupport ≡ canonicalImportedNSF7FiniteStatisticalSupport
    premises :
      List TransferOperatorBiasNeutralityPremise
    premisesAreCanonical :
      premises ≡ canonicalTransferOperatorBiasNeutralityPremises
    premiseCountIsSix :
      transferOperatorBiasNeutralityPremiseCount ≡ 6
    conditionals :
      List TransferOperatorBiasNeutralityConditional
    conditionalsAreCanonical :
      conditionals ≡ canonicalTransferOperatorBiasNeutralityConditionals
    conditionalCountIsFive :
      transferOperatorBiasNeutralityConditionalCount ≡ 5
    consequences :
      List TransferOperatorBiasNeutralityConsequence
    consequencesAreCanonical :
      consequences ≡ canonicalTransferOperatorBiasNeutralityConsequences
    consequenceCountIsFive :
      transferOperatorBiasNeutralityConsequenceCount ≡ 5
    consequenceText :
      String
    consequenceTextIsCanonical :
      consequenceText ≡ biasMuRConsequenceText
    conditionalText :
      String
    conditionalTextIsCanonical :
      conditionalText ≡ conditionalClaimText
    blockers :
      List TransferOperatorBiasNeutralityBlocker
    blockersAreCanonical :
      blockers ≡ canonicalTransferOperatorBiasNeutralityBlockers
    blockerCountIsSix :
      transferOperatorBiasNeutralityBlockerCount ≡ 6
    finiteStatisticalClaimConditionalIsTrue :
      finiteStatisticalClaimConditional ≡ true
    arcsineOutputConditionDischargedHereIsFalse :
      arcsineOutputConditionDischargedHere ≡ false
    lambdaKappaIndependenceProvedHereIsFalse :
      lambdaKappaIndependenceProvedHere ≡ false
    typeIBiasBoundPromotedIsFalse :
      typeIBiasBoundPromoted ≡ false
    pdeTransferPromotedIsFalse :
      pdeTransferPromoted ≡ false
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionIsFalse :
      terminalPromotion ≡ false
    summary :
      String
    summaryIsCanonical :
      summary ≡ nsTransferOperatorBiasNeutralitySummary

canonicalNSTransferOperatorBiasNeutralityBoundary :
  NSTransferOperatorBiasNeutralityBoundary
canonicalNSTransferOperatorBiasNeutralityBoundary =
  record
    { status =
        nsF7TransferOperatorBiasNeutralityRecorded_conditionalFinite_noPromotion
    ; statusIsCanonical =
        refl
    ; finiteSupport =
        canonicalImportedNSF7FiniteStatisticalSupport
    ; finiteSupportIsCanonical =
        refl
    ; premises =
        canonicalTransferOperatorBiasNeutralityPremises
    ; premisesAreCanonical =
        refl
    ; premiseCountIsSix =
        refl
    ; conditionals =
        canonicalTransferOperatorBiasNeutralityConditionals
    ; conditionalsAreCanonical =
        refl
    ; conditionalCountIsFive =
        refl
    ; consequences =
        canonicalTransferOperatorBiasNeutralityConsequences
    ; consequencesAreCanonical =
        refl
    ; consequenceCountIsFive =
        refl
    ; consequenceText =
        biasMuRConsequenceText
    ; consequenceTextIsCanonical =
        refl
    ; conditionalText =
        conditionalClaimText
    ; conditionalTextIsCanonical =
        refl
    ; blockers =
        canonicalTransferOperatorBiasNeutralityBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCountIsSix =
        refl
    ; finiteStatisticalClaimConditionalIsTrue =
        refl
    ; arcsineOutputConditionDischargedHereIsFalse =
        refl
    ; lambdaKappaIndependenceProvedHereIsFalse =
        refl
    ; typeIBiasBoundPromotedIsFalse =
        refl
    ; pdeTransferPromotedIsFalse =
        refl
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalPromotionIsFalse =
        refl
    ; summary =
        nsTransferOperatorBiasNeutralitySummary
    ; summaryIsCanonical =
        refl
    }

nsTransferOperatorBiasNeutralityKeepsTypeIFalse :
  typeIBiasBoundPromoted ≡ false
nsTransferOperatorBiasNeutralityKeepsTypeIFalse =
  refl

nsTransferOperatorBiasNeutralityKeepsPDEFalse :
  pdeTransferPromoted ≡ false
nsTransferOperatorBiasNeutralityKeepsPDEFalse =
  refl

nsTransferOperatorBiasNeutralityKeepsClayFalse :
  clayNavierStokesPromoted ≡ false
nsTransferOperatorBiasNeutralityKeepsClayFalse =
  refl

nsTransferOperatorBiasNeutralityKeepsTerminalFalse :
  terminalPromotion ≡ false
nsTransferOperatorBiasNeutralityKeepsTerminalFalse =
  refl
