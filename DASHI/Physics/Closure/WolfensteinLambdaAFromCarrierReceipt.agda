module DASHI.Physics.Closure.WolfensteinLambdaAFromCarrierReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CabibboAngleCarrierReceipt as Cabibbo
import DASHI.Physics.Closure.CKMVusCarrierPredictionTargetReceipt as Vus
import DASHI.Physics.Closure.CarrierYukawaRatioTargetReceipt as Ratios
import DASHI.Physics.YM.WolfensteinCKM as Wolf

------------------------------------------------------------------------
-- Wolfenstein lambda/A carrier diagnostics.
--
-- This receipt records the closed-form carrier readbacks
--
--   lambda = alpha1*pi*sqrt(3) ~= 0.224403
--   A      = 112/(9*pi*sqrt(24)) ~= 0.8086
--
-- as comparison-only diagnostics.  It deliberately does not promote these
-- readbacks to physical CKM/Wolfenstein parameters; rho and eta remain open.

data WolfensteinLambdaAFromCarrierStatus : Set where
  wolfensteinLambdaADiagnosticsRecordedComparisonOnly :
    WolfensteinLambdaAFromCarrierStatus

data WolfensteinLambdaAOpenParameter : Set where
  rhoParameterOpen :
    WolfensteinLambdaAOpenParameter

  etaParameterOpen :
    WolfensteinLambdaAOpenParameter

canonicalWolfensteinLambdaAOpenParameters :
  List WolfensteinLambdaAOpenParameter
canonicalWolfensteinLambdaAOpenParameters =
  rhoParameterOpen
  ∷ etaParameterOpen
  ∷ []

data WolfensteinLambdaABlocker : Set where
  missingAcceptedCommonAlphaForLambda :
    WolfensteinLambdaABlocker

  missingApproximationErrorBoundForLambda :
    WolfensteinLambdaABlocker

  missingPhysicalWolfensteinAAuthority :
    WolfensteinLambdaABlocker

  missingRhoCarrierDiagnostic :
    WolfensteinLambdaABlocker

  missingEtaCarrierDiagnostic :
    WolfensteinLambdaABlocker

  missingNonIdentityPhysicalCKMDiagonalizers :
    WolfensteinLambdaABlocker

  missingPDGWolfensteinAuthorityBinding :
    WolfensteinLambdaABlocker

canonicalWolfensteinLambdaABlockers :
  List WolfensteinLambdaABlocker
canonicalWolfensteinLambdaABlockers =
  missingAcceptedCommonAlphaForLambda
  ∷ missingApproximationErrorBoundForLambda
  ∷ missingPhysicalWolfensteinAAuthority
  ∷ missingRhoCarrierDiagnostic
  ∷ missingEtaCarrierDiagnostic
  ∷ missingNonIdentityPhysicalCKMDiagonalizers
  ∷ missingPDGWolfensteinAuthorityBinding
  ∷ []

lambdaCarrierFormula : String
lambdaCarrierFormula =
  "lambda = alpha1*pi*sqrt(3)"

lambdaCarrierApproxLabel : String
lambdaCarrierApproxLabel =
  "lambda ~= 0.224403 from alpha1*pi*sqrt(3)"

aCarrierFormula : String
aCarrierFormula =
  "A = 112/(9*pi*sqrt(24))"

aCarrierApproxLabel : String
aCarrierApproxLabel =
  "A ~= 0.8086 from 112/(9*pi*sqrt(24))"

pdgLambdaComparisonLabel : String
pdgLambdaComparisonLabel =
  "PDG-sized Wolfenstein lambda comparison target ~= 0.225"

pdgAComparisonLabel : String
pdgAComparisonLabel =
  "PDG-sized Wolfenstein A comparison target ~= 0.826"

record WolfensteinLambdaADiagnostics : Setω where
  field
    alpha1PartsPerMillion :
      Nat

    alpha1PartsPerMillionMatchesCarrierRatioReceipt :
      alpha1PartsPerMillion
      ≡
      Ratios.alphaFromUpOverCharmPartsPerMillion
        Ratios.canonicalAlphaFromFermionMassRatioEstimateReceipt

    lambdaFormula :
      String

    lambdaFormulaIsCarrierClosedForm :
      lambdaFormula ≡ lambdaCarrierFormula

    lambdaPartsPerMillion :
      Nat

    lambdaPartsPerMillionIsCanonicalDiagnostic :
      lambdaPartsPerMillion ≡ 224403

    lambdaApproximationLabel :
      String

    lambdaApproximationLabelIsCanonical :
      lambdaApproximationLabel ≡ lambdaCarrierApproxLabel

    aFormula :
      String

    aFormulaIsCarrierClosedForm :
      aFormula ≡ aCarrierFormula

    aPartsPerTenThousand :
      Nat

    aPartsPerTenThousandIsCanonicalDiagnostic :
      aPartsPerTenThousand ≡ 8086

    aApproximationLabel :
      String

    aApproximationLabelIsCanonical :
      aApproximationLabel ≡ aCarrierApproxLabel

    closedFormCarrierDiagnosticsRecorded :
      Bool

    closedFormCarrierDiagnosticsRecordedIsTrue :
      closedFormCarrierDiagnosticsRecorded ≡ true

    diagnosticsPromotedToPhysicalWolfensteinParameters :
      Bool

    diagnosticsPromotedToPhysicalWolfensteinParametersIsFalse :
      diagnosticsPromotedToPhysicalWolfensteinParameters ≡ false

    diagnosticsBoundary :
      List String

open WolfensteinLambdaADiagnostics public

canonicalWolfensteinLambdaADiagnostics :
  WolfensteinLambdaADiagnostics
canonicalWolfensteinLambdaADiagnostics =
  record
    { alpha1PartsPerMillion =
        Ratios.alphaFromUpOverCharmPartsPerMillion
          Ratios.canonicalAlphaFromFermionMassRatioEstimateReceipt
    ; alpha1PartsPerMillionMatchesCarrierRatioReceipt =
        refl
    ; lambdaFormula =
        lambdaCarrierFormula
    ; lambdaFormulaIsCarrierClosedForm =
        refl
    ; lambdaPartsPerMillion =
        224403
    ; lambdaPartsPerMillionIsCanonicalDiagnostic =
        refl
    ; lambdaApproximationLabel =
        lambdaCarrierApproxLabel
    ; lambdaApproximationLabelIsCanonical =
        refl
    ; aFormula =
        aCarrierFormula
    ; aFormulaIsCarrierClosedForm =
        refl
    ; aPartsPerTenThousand =
        8086
    ; aPartsPerTenThousandIsCanonicalDiagnostic =
        refl
    ; aApproximationLabel =
        aCarrierApproxLabel
    ; aApproximationLabelIsCanonical =
        refl
    ; closedFormCarrierDiagnosticsRecorded =
        true
    ; closedFormCarrierDiagnosticsRecordedIsTrue =
        refl
    ; diagnosticsPromotedToPhysicalWolfensteinParameters =
        false
    ; diagnosticsPromotedToPhysicalWolfensteinParametersIsFalse =
        refl
    ; diagnosticsBoundary =
        "lambda is recorded as alpha1*pi*sqrt(3), with alpha1 threaded from CarrierYukawaRatioTargetReceipt"
        ∷ "lambdaPartsPerMillion=224403 records the approximate closed-form diagnostic 0.224403"
        ∷ "A is recorded as 112/(9*pi*sqrt(24)) with aPartsPerTenThousand=8086"
        ∷ "These are carrier diagnostics only, not accepted physical Wolfenstein parameters"
        ∷ []
    }

record WolfensteinLambdaAPDGComparison : Setω where
  field
    pdgLambdaComparison :
      String

    pdgLambdaComparisonIsCanonical :
      pdgLambdaComparison ≡ pdgLambdaComparisonLabel

    pdgLambdaPartsPerMillion :
      Nat

    pdgLambdaPartsPerMillionIsComparisonTarget :
      pdgLambdaPartsPerMillion ≡ 225000

    carrierLambdaPartsPerMillion :
      Nat

    carrierLambdaPartsPerMillionMatchesDiagnostics :
      carrierLambdaPartsPerMillion
      ≡
      lambdaPartsPerMillion canonicalWolfensteinLambdaADiagnostics

    pdgAComparison :
      String

    pdgAComparisonIsCanonical :
      pdgAComparison ≡ pdgAComparisonLabel

    pdgAPartsPerMillion :
      Nat

    pdgAPartsPerMillionIsComparisonTarget :
      pdgAPartsPerMillion ≡ 826000

    carrierAPartsPerTenThousand :
      Nat

    carrierAPartsPerTenThousandMatchesDiagnostics :
      carrierAPartsPerTenThousand
      ≡
      aPartsPerTenThousand canonicalWolfensteinLambdaADiagnostics

    pdgComparisonsRecorded :
      Bool

    pdgComparisonsRecordedIsTrue :
      pdgComparisonsRecorded ≡ true

    pdgAuthorityBindingPromoted :
      Bool

    pdgAuthorityBindingPromotedIsFalse :
      pdgAuthorityBindingPromoted ≡ false

    comparisonBoundary :
      List String

open WolfensteinLambdaAPDGComparison public

canonicalWolfensteinLambdaAPDGComparison :
  WolfensteinLambdaAPDGComparison
canonicalWolfensteinLambdaAPDGComparison =
  record
    { pdgLambdaComparison =
        pdgLambdaComparisonLabel
    ; pdgLambdaComparisonIsCanonical =
        refl
    ; pdgLambdaPartsPerMillion =
        225000
    ; pdgLambdaPartsPerMillionIsComparisonTarget =
        refl
    ; carrierLambdaPartsPerMillion =
        lambdaPartsPerMillion canonicalWolfensteinLambdaADiagnostics
    ; carrierLambdaPartsPerMillionMatchesDiagnostics =
        refl
    ; pdgAComparison =
        pdgAComparisonLabel
    ; pdgAComparisonIsCanonical =
        refl
    ; pdgAPartsPerMillion =
        826000
    ; pdgAPartsPerMillionIsComparisonTarget =
        refl
    ; carrierAPartsPerTenThousand =
        aPartsPerTenThousand canonicalWolfensteinLambdaADiagnostics
    ; carrierAPartsPerTenThousandMatchesDiagnostics =
        refl
    ; pdgComparisonsRecorded =
        true
    ; pdgComparisonsRecordedIsTrue =
        refl
    ; pdgAuthorityBindingPromoted =
        false
    ; pdgAuthorityBindingPromotedIsFalse =
        refl
    ; comparisonBoundary =
        "lambda 0.224403 is recorded next to the existing PDG-sized |V_us|/lambda comparison target near 0.225"
        ∷ "A 0.8086 is recorded next to a PDG-sized Wolfenstein A comparison target near 0.826"
        ∷ "The comparison is diagnostic only; no PDG authority binding or error-bound proof is constructed"
        ∷ []
    }

record WolfensteinLambdaAFromCarrierReceipt : Setω where
  field
    status :
      WolfensteinLambdaAFromCarrierStatus

    cabibboCarrierReceipt :
      Cabibbo.CabibboAngleCarrierReceipt

    cabibboCarrierReceiptIsCanonical :
      Bool

    cabibboCarrierReceiptIsCanonicalIsTrue :
      cabibboCarrierReceiptIsCanonical ≡ true

    vusTargetReceipt :
      Vus.CKMVusCarrierPredictionTargetReceipt

    vusTargetReceiptIsCanonical :
      Bool

    vusTargetReceiptIsCanonicalIsTrue :
      vusTargetReceiptIsCanonical ≡ true

    wolfensteinWitness :
      Wolf.WolfensteinCKMWitness

    wolfensteinWitnessIsCanonical :
      Bool

    wolfensteinWitnessIsCanonicalIsTrue :
      wolfensteinWitnessIsCanonical ≡ true

    diagnostics :
      WolfensteinLambdaADiagnostics

    diagnosticsAreCanonical :
      Bool

    diagnosticsAreCanonicalIsTrue :
      diagnosticsAreCanonical ≡ true

    pdgComparison :
      WolfensteinLambdaAPDGComparison

    pdgComparisonIsCanonical :
      Bool

    pdgComparisonIsCanonicalIsTrue :
      pdgComparisonIsCanonical ≡ true

    openParameters :
      List WolfensteinLambdaAOpenParameter

    openParametersAreCanonical :
      openParameters ≡ canonicalWolfensteinLambdaAOpenParameters

    rhoCarrierDiagnosticSupplied :
      Bool

    rhoCarrierDiagnosticSuppliedIsFalse :
      rhoCarrierDiagnosticSupplied ≡ false

    etaCarrierDiagnosticSupplied :
      Bool

    etaCarrierDiagnosticSuppliedIsFalse :
      etaCarrierDiagnosticSupplied ≡ false

    physicalLambdaPromoted :
      Bool

    physicalLambdaPromotedIsFalse :
      physicalLambdaPromoted ≡ false

    physicalAPromoted :
      Bool

    physicalAPromotedIsFalse :
      physicalAPromoted ≡ false

    physicalRhoEtaPromoted :
      Bool

    physicalRhoEtaPromotedIsFalse :
      physicalRhoEtaPromoted ≡ false

    physicalCKMPromotionConstructed :
      Bool

    physicalCKMPromotionConstructedMatchesVusReceipt :
      physicalCKMPromotionConstructed
      ≡
      Vus.physicalCKMPromotionConstructed vusTargetReceipt

    physicalCKMPromotionConstructedIsFalse :
      physicalCKMPromotionConstructed ≡ false

    physicalYukawaRatioPredictionsPromoted :
      Bool

    physicalYukawaRatioPredictionsPromotedMatchesCabibboReceipt :
      physicalYukawaRatioPredictionsPromoted
      ≡
      Cabibbo.physicalYukawaRatioPredictionsPromoted cabibboCarrierReceipt

    physicalYukawaRatioPredictionsPromotedIsFalse :
      physicalYukawaRatioPredictionsPromoted ≡ false

    pdgAuthorityBindingPromoted :
      Bool

    pdgAuthorityBindingPromotedMatchesComparison :
      pdgAuthorityBindingPromoted
      ≡
      WolfensteinLambdaAPDGComparison.pdgAuthorityBindingPromoted pdgComparison

    pdgAuthorityBindingPromotedIsFalse :
      pdgAuthorityBindingPromoted ≡ false

    terminalPromotionConstructed :
      Bool

    terminalPromotionConstructedIsFalse :
      terminalPromotionConstructed ≡ false

    blockers :
      List WolfensteinLambdaABlocker

    blockersAreCanonical :
      blockers ≡ canonicalWolfensteinLambdaABlockers

    receiptBoundary :
      List String

open WolfensteinLambdaAFromCarrierReceipt public

canonicalWolfensteinLambdaAFromCarrierReceipt :
  WolfensteinLambdaAFromCarrierReceipt
canonicalWolfensteinLambdaAFromCarrierReceipt =
  record
    { status =
        wolfensteinLambdaADiagnosticsRecordedComparisonOnly
    ; cabibboCarrierReceipt =
        Cabibbo.canonicalCabibboAngleCarrierReceipt
    ; cabibboCarrierReceiptIsCanonical =
        true
    ; cabibboCarrierReceiptIsCanonicalIsTrue =
        refl
    ; vusTargetReceipt =
        Vus.canonicalCKMVusCarrierPredictionTargetReceipt
    ; vusTargetReceiptIsCanonical =
        true
    ; vusTargetReceiptIsCanonicalIsTrue =
        refl
    ; wolfensteinWitness =
        Wolf.canonicalWolfensteinCKMWitness
    ; wolfensteinWitnessIsCanonical =
        true
    ; wolfensteinWitnessIsCanonicalIsTrue =
        refl
    ; diagnostics =
        canonicalWolfensteinLambdaADiagnostics
    ; diagnosticsAreCanonical =
        true
    ; diagnosticsAreCanonicalIsTrue =
        refl
    ; pdgComparison =
        canonicalWolfensteinLambdaAPDGComparison
    ; pdgComparisonIsCanonical =
        true
    ; pdgComparisonIsCanonicalIsTrue =
        refl
    ; openParameters =
        canonicalWolfensteinLambdaAOpenParameters
    ; openParametersAreCanonical =
        refl
    ; rhoCarrierDiagnosticSupplied =
        false
    ; rhoCarrierDiagnosticSuppliedIsFalse =
        refl
    ; etaCarrierDiagnosticSupplied =
        false
    ; etaCarrierDiagnosticSuppliedIsFalse =
        refl
    ; physicalLambdaPromoted =
        false
    ; physicalLambdaPromotedIsFalse =
        refl
    ; physicalAPromoted =
        false
    ; physicalAPromotedIsFalse =
        refl
    ; physicalRhoEtaPromoted =
        false
    ; physicalRhoEtaPromotedIsFalse =
        refl
    ; physicalCKMPromotionConstructed =
        Vus.physicalCKMPromotionConstructed
          Vus.canonicalCKMVusCarrierPredictionTargetReceipt
    ; physicalCKMPromotionConstructedMatchesVusReceipt =
        refl
    ; physicalCKMPromotionConstructedIsFalse =
        Vus.physicalCKMPromotionConstructedIsFalse
          Vus.canonicalCKMVusCarrierPredictionTargetReceipt
    ; physicalYukawaRatioPredictionsPromoted =
        Cabibbo.physicalYukawaRatioPredictionsPromoted
          Cabibbo.canonicalCabibboAngleCarrierReceipt
    ; physicalYukawaRatioPredictionsPromotedMatchesCabibboReceipt =
        refl
    ; physicalYukawaRatioPredictionsPromotedIsFalse =
        Cabibbo.physicalYukawaRatioPredictionsPromotedIsFalse
          Cabibbo.canonicalCabibboAngleCarrierReceipt
    ; pdgAuthorityBindingPromoted =
        WolfensteinLambdaAPDGComparison.pdgAuthorityBindingPromoted
          canonicalWolfensteinLambdaAPDGComparison
    ; pdgAuthorityBindingPromotedMatchesComparison =
        refl
    ; pdgAuthorityBindingPromotedIsFalse =
        WolfensteinLambdaAPDGComparison.pdgAuthorityBindingPromotedIsFalse
          canonicalWolfensteinLambdaAPDGComparison
    ; terminalPromotionConstructed =
        false
    ; terminalPromotionConstructedIsFalse =
        refl
    ; blockers =
        canonicalWolfensteinLambdaABlockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        "This receipt records lambda=alpha1*pi*sqrt(3) ~= 0.224403 as a closed-form carrier diagnostic"
        ∷ "This receipt records A=112/(9*pi*sqrt(24)) ~= 0.8086 as a closed-form carrier diagnostic"
        ∷ "The lambda diagnostic threads alpha1 from the existing carrier-Yukawa ratio readback and sits next to the Cabibbo/Vus comparison lane"
        ∷ "PDG lambda and A values are comparison targets only; no authority binding or accepted error-bound theorem is supplied"
        ∷ "rho and eta remain open parameters"
        ∷ "All physical, CKM, Wolfenstein, PDG-authority, rho/eta, and terminal promotion flags remain false"
        ∷ []
    }

wolfensteinLambdaAReceiptRecordsLambdaDiagnostic :
  lambdaPartsPerMillion
    (diagnostics canonicalWolfensteinLambdaAFromCarrierReceipt)
  ≡
  224403
wolfensteinLambdaAReceiptRecordsLambdaDiagnostic =
  refl

wolfensteinLambdaAReceiptRecordsADiagnostic :
  aPartsPerTenThousand
    (diagnostics canonicalWolfensteinLambdaAFromCarrierReceipt)
  ≡
  8086
wolfensteinLambdaAReceiptRecordsADiagnostic =
  refl

wolfensteinLambdaAReceiptKeepsRhoOpen :
  rhoCarrierDiagnosticSupplied canonicalWolfensteinLambdaAFromCarrierReceipt
  ≡
  false
wolfensteinLambdaAReceiptKeepsRhoOpen =
  refl

wolfensteinLambdaAReceiptKeepsEtaOpen :
  etaCarrierDiagnosticSupplied canonicalWolfensteinLambdaAFromCarrierReceipt
  ≡
  false
wolfensteinLambdaAReceiptKeepsEtaOpen =
  refl

wolfensteinLambdaAReceiptKeepsPhysicalPromotionClosed :
  physicalCKMPromotionConstructed canonicalWolfensteinLambdaAFromCarrierReceipt
  ≡
  false
wolfensteinLambdaAReceiptKeepsPhysicalPromotionClosed =
  Vus.physicalCKMPromotionConstructedIsFalse
    Vus.canonicalCKMVusCarrierPredictionTargetReceipt
