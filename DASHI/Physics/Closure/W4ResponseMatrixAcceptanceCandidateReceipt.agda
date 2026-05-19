module DASHI.Physics.Closure.W4ResponseMatrixAcceptanceCandidateReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat.Base using (_<_)
open import Data.Nat.Properties as NatP using (m≤m+n)

------------------------------------------------------------------------
-- Non-promoting W4 response-matrix acceptance-candidate receipt.
--
-- The public CMS-SMP-20-003 / HEPData ins2079374 phi-star response
-- matrices t68-t77 are cached locally and bound by SHA-256 in the Python
-- diagnostic output.  This module records the local arithmetic candidates:
--
--   A_col[j]  = sum_i P[i][j]
--   A_diag[j] = P[j][j]
--
-- It deliberately does not construct a W4 promotion receipt.  Promotion still
-- requires a typed gate consumer accepting one candidate as the W4 A(M,phi*)
-- bridge, with channel combination and covariance propagation conventions.

data W4ResponseMatrixAcceptanceCandidateStatus : Set where
  columnSumAndDiagonalCandidatesComputedNonPromoting :
    W4ResponseMatrixAcceptanceCandidateStatus
  diagonalConventionAcceptedNonPromoting :
    W4ResponseMatrixAcceptanceCandidateStatus

data W4ResponseMatrixAcceptanceCandidateFirstMissing : Set where
  missingAcceptedDiagonalConventionGateConsumer :
    W4ResponseMatrixAcceptanceCandidateFirstMissing
  missingTypedGateConsumerForResponseMatrixAcceptanceCandidate :
    W4ResponseMatrixAcceptanceCandidateFirstMissing
  missingW4ZAdequacyConsumer :
    W4ResponseMatrixAcceptanceCandidateFirstMissing

data W4ResponseMatrixAcceptanceCandidateChoice : Set where
  columnSumCandidate :
    W4ResponseMatrixAcceptanceCandidateChoice
  diagonalCandidate :
    W4ResponseMatrixAcceptanceCandidateChoice
  noAcceptedCandidate :
    W4ResponseMatrixAcceptanceCandidateChoice

data W4ResponseMatrixChannelCombinationRule : Set where
  separateElectronMuonChannels :
    W4ResponseMatrixChannelCombinationRule
  weightedElectronMuonCombination :
    W4ResponseMatrixChannelCombinationRule
  geometricMeanElectronMuonCombination :
    W4ResponseMatrixChannelCombinationRule
  noAcceptedChannelCombinationRule :
    W4ResponseMatrixChannelCombinationRule

data W4ResponseMatrixAcceptanceCandidateField : Set where
  sourceRecordPointer :
    W4ResponseMatrixAcceptanceCandidateField
  cmsMirrorPointer :
    W4ResponseMatrixAcceptanceCandidateField
  diagnosticRunnerPointer :
    W4ResponseMatrixAcceptanceCandidateField
  diagnosticOutputPointer :
    W4ResponseMatrixAcceptanceCandidateField
  checksumManifestPointer :
    W4ResponseMatrixAcceptanceCandidateField
  columnSumCandidateFormula :
    W4ResponseMatrixAcceptanceCandidateField
  diagonalCandidateFormula :
    W4ResponseMatrixAcceptanceCandidateField
  columnSumRoundoffBound :
    W4ResponseMatrixAcceptanceCandidateField
  diagonalBound :
    W4ResponseMatrixAcceptanceCandidateField
  diagonalW4WindowValues :
    W4ResponseMatrixAcceptanceCandidateField
  channelCombinationRuleCandidate :
    W4ResponseMatrixAcceptanceCandidateField
  diagnosticOutputChecksum :
    W4ResponseMatrixAcceptanceCandidateField
  typedGateConsumerStillMissing :
    W4ResponseMatrixAcceptanceCandidateField

data W4ZInternalAdequacyEvidenceStatus : Set where
  computedAdequacyEvidenceNonPromoting :
    W4ZInternalAdequacyEvidenceStatus

data W4ZInternalAdequacyEvidenceFirstMissing : Set where
  missingScaledDecimalStrictGreaterThanPrimitive :
    W4ZInternalAdequacyEvidenceFirstMissing
  internalAdequacyArithmeticDischargedW4ZAdequacyPending :
    W4ZInternalAdequacyEvidenceFirstMissing

scaledDecimalStrictGreaterThan9566over9000 :
  9000 < 9566
scaledDecimalStrictGreaterThan9566over9000 =
  NatP.m≤m+n 9001 565

canonicalW4ResponseMatrixAcceptanceCandidateFields :
  List W4ResponseMatrixAcceptanceCandidateField
canonicalW4ResponseMatrixAcceptanceCandidateFields =
  sourceRecordPointer
  ∷ cmsMirrorPointer
  ∷ diagnosticRunnerPointer
  ∷ diagnosticOutputPointer
  ∷ checksumManifestPointer
  ∷ columnSumCandidateFormula
  ∷ diagonalCandidateFormula
  ∷ columnSumRoundoffBound
  ∷ diagonalBound
  ∷ diagonalW4WindowValues
  ∷ channelCombinationRuleCandidate
  ∷ diagnosticOutputChecksum
  ∷ typedGateConsumerStillMissing
  ∷ []

record W4ResponseMatrixAcceptanceCandidateReceipt : Set where
  field
    status :
      W4ResponseMatrixAcceptanceCandidateStatus

    firstMissing :
      W4ResponseMatrixAcceptanceCandidateFirstMissing

    sourceRecord :
      String

    cmsMirror :
      String

    diagnosticRunner :
      String

    diagnosticOutput :
      String

    checksumManifest :
      String

    outputSchema :
      String

    diagnosticOutputSHA256 :
      String

    columnSumCandidateFormulaText :
      String

    diagonalCandidateFormulaText :
      String

    selectedCandidateForGate :
      W4ResponseMatrixAcceptanceCandidateChoice

    channelCombinationRule :
      W4ResponseMatrixChannelCombinationRule

    channelCombinationRuleText :
      String

    electronDiagonalMean50to76 :
      String

    muonDiagonalMean50to76 :
      String

    electronDiagonalMean76to106 :
      String

    muonDiagonalMean76to106 :
      String

    electronDiagonalMean106to170 :
      String

    muonDiagonalMean106to170 :
      String

    selectedW4DiagonalGlobalMin :
      String

    selectedW4DiagonalGlobalMax :
      String

    selectedW4DiagonalGlobalMean :
      String

    selectedW4DiagonalAdmissibilityBound :
      String

    columnSumMaxAbsGapToOne :
      String

    allColumnSumCandidatesBoundedWithRoundoff :
      Bool

    allColumnSumCandidatesBoundedWithRoundoffIsTrue :
      allColumnSumCandidatesBoundedWithRoundoff ≡ true

    allDiagonalCandidatesBounded :
      Bool

    allDiagonalCandidatesBoundedIsTrue :
      allDiagonalCandidatesBounded ≡ true

    directAcceptanceSurfacePresent :
      Bool

    directAcceptanceSurfacePresentIsFalse :
      directAcceptanceSurfacePresent ≡ false

    acceptedDiagonalConventionPresent :
      Bool

    acceptedDiagonalConventionPresentIsTrue :
      acceptedDiagonalConventionPresent ≡ true

    acceptedChannelCombinationPresent :
      Bool

    acceptedChannelCombinationPresentIsTrue :
      acceptedChannelCombinationPresent ≡ true

    covariancePropagationLawPresent :
      Bool

    covariancePropagationLawPresentIsTrue :
      covariancePropagationLawPresent ≡ true

    constructsW4GateReceipt :
      Bool

    constructsW4GateReceiptIsFalse :
      constructsW4GateReceipt ≡ false

    notes :
      List String

    receiptFields :
      List W4ResponseMatrixAcceptanceCandidateField

    receiptFieldsAreCanonical :
      receiptFields ≡ canonicalW4ResponseMatrixAcceptanceCandidateFields

record W4ZInternalAdequacyEvidenceReceipt : Set where
  field
    status :
      W4ZInternalAdequacyEvidenceStatus

    firstMissing :
      W4ZInternalAdequacyEvidenceFirstMissing

    sourceCandidateReceipt :
      W4ResponseMatrixAcceptanceCandidateReceipt

    massWindow :
      String

    channelCombinationRule :
      W4ResponseMatrixChannelCombinationRule

    combinedDiagonalEfficiency :
      String

    combinedDiagonalEfficiencyScaled1e4 :
      String

    adequacyBound :
      String

    adequacyBoundScaled1e4 :
      String

    scaledDecimalStrictGreaterThanPrimitive :
      String

    scaledDecimalStrictGreaterThanWitness :
      9000 < 9566

    computedPassBoolean :
      Bool

    computedPassBooleanIsTrue :
      computedPassBoolean ≡ true

    constructsW4ZAdequacy :
      Bool

    constructsW4ZAdequacyIsFalse :
      constructsW4ZAdequacy ≡ false

    constructsW4GateReceipt :
      Bool

    constructsW4GateReceiptIsFalse :
      constructsW4GateReceipt ≡ false

    evidenceBoundary :
      List String

canonicalW4ResponseMatrixAcceptanceCandidateReceipt :
  W4ResponseMatrixAcceptanceCandidateReceipt
canonicalW4ResponseMatrixAcceptanceCandidateReceipt =
  record
    { status =
        diagonalConventionAcceptedNonPromoting
    ; firstMissing =
        missingW4ZAdequacyConsumer
    ; sourceRecord =
        "HEPData ins2079374 / CMS-SMP-20-003"
    ; cmsMirror =
        "https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/SMP-20-003_hepdata/"
    ; diagnosticRunner =
        "scripts/run_w4w5_hepdata_response_matrix_diagnostic.py"
    ; diagnosticOutput =
        "scripts/data/outputs/w4w5_hepdata_response_matrix_diagnostic.json"
    ; checksumManifest =
        "scripts/data/hepdata/ins2079374_response_phistar_t68_t77.sha256"
    ; outputSchema =
        "dashi-w4w5-hepdata-response-matrix-diagnostic-v2"
    ; diagnosticOutputSHA256 =
        "366fe83fe4dae1d14ccb9ef3bd7a0858fa8baf9998fc8c96250c16bc4a748fdb"
    ; columnSumCandidateFormulaText =
        "A_col[j] = sum_i P[i][j]"
    ; diagonalCandidateFormulaText =
        "A_diag[j] = P[j][j]"
    ; selectedCandidateForGate =
        diagonalCandidate
    ; channelCombinationRule =
        geometricMeanElectronMuonCombination
    ; channelCombinationRuleText =
        "Accepted W4 convention-layer channel rule: A_geom[j] = sqrt(A_e,j * A_mu,j), geometric mean of the electron and muon same-bin diagonal candidates"
    ; electronDiagonalMean50to76 =
        "0.9216377777777777"
    ; muonDiagonalMean50to76 =
        "0.9835272222222221"
    ; electronDiagonalMean76to106 =
        "0.9277322222222223"
    ; muonDiagonalMean76to106 =
        "0.9857633333333333"
    ; electronDiagonalMean106to170 =
        "0.9344861111111111"
    ; muonDiagonalMean106to170 =
        "0.9885316666666666"
    ; selectedW4DiagonalGlobalMin =
        "0.8279"
    ; selectedW4DiagonalGlobalMax =
        "1.0"
    ; selectedW4DiagonalGlobalMean =
        "0.9569463888888888"
    ; selectedW4DiagonalAdmissibilityBound =
        "For W4-selected windows 50-76, 76-106, and 106-170 GeV, all electron/muon diagonal entries satisfy 0 <= A_diag[j] <= 1; observed global min=0.8279, max=1.0"
    ; columnSumMaxAbsGapToOne =
        "1.910199999999307e-05 across all t68-t77 matrices; W4-selected windows are within 5.679599999974805e-06"
    ; allColumnSumCandidatesBoundedWithRoundoff =
        true
    ; allColumnSumCandidatesBoundedWithRoundoffIsTrue =
        refl
    ; allDiagonalCandidatesBounded =
        true
    ; allDiagonalCandidatesBoundedIsTrue =
        refl
    ; directAcceptanceSurfacePresent =
        false
    ; directAcceptanceSurfacePresentIsFalse =
        refl
    ; acceptedDiagonalConventionPresent =
        true
    ; acceptedDiagonalConventionPresentIsTrue =
        refl
    ; acceptedChannelCombinationPresent =
        true
    ; acceptedChannelCombinationPresentIsTrue =
        refl
    ; covariancePropagationLawPresent =
        true
    ; covariancePropagationLawPresentIsTrue =
        refl
    ; constructsW4GateReceipt =
        false
    ; constructsW4GateReceiptIsFalse =
        refl
    ; notes =
        "Column sums are numerically one within roundoff, consistent with a normalized migration matrix"
        ∷ "Diagonal entries are bounded in [0,1] and are accepted here as the W4 convention-layer same-bin retention surface"
        ∷ "The W4-relevant diagonal mean candidates are recorded separately for electron and muon channels in 50-76, 76-106, and 106-170 GeV"
        ∷ "The accepted convention-layer electron/muon combination is the geometric mean A_geom[j] = sqrt(A_e,j * A_mu,j)"
        ∷ "The accepted convention-layer covariance propagation is the linearized corrected-ratio Jacobian law recorded in W4DiagonalConventionGateConsumer"
        ∷ "No W4ZAdequacy consumer accepts this convention layer yet"
        ∷ []
    ; receiptFields =
        canonicalW4ResponseMatrixAcceptanceCandidateFields
    ; receiptFieldsAreCanonical =
        refl
    }

canonicalW4ResponseMatrixAcceptanceCandidateDoesNotPromoteW4 :
  W4ResponseMatrixAcceptanceCandidateReceipt.constructsW4GateReceipt
    canonicalW4ResponseMatrixAcceptanceCandidateReceipt
  ≡ false
canonicalW4ResponseMatrixAcceptanceCandidateDoesNotPromoteW4 =
  W4ResponseMatrixAcceptanceCandidateReceipt.constructsW4GateReceiptIsFalse
    canonicalW4ResponseMatrixAcceptanceCandidateReceipt

canonicalW4ZInternalAdequacyEvidenceReceipt :
  W4ZInternalAdequacyEvidenceReceipt
canonicalW4ZInternalAdequacyEvidenceReceipt =
  record
    { status =
        computedAdequacyEvidenceNonPromoting
    ; firstMissing =
        internalAdequacyArithmeticDischargedW4ZAdequacyPending
    ; sourceCandidateReceipt =
        canonicalW4ResponseMatrixAcceptanceCandidateReceipt
    ; massWindow =
        "76-106 GeV"
    ; channelCombinationRule =
        geometricMeanElectronMuonCombination
    ; combinedDiagonalEfficiency =
        "0.9566"
    ; combinedDiagonalEfficiencyScaled1e4 =
        "9566"
    ; adequacyBound =
        "0.90"
    ; adequacyBoundScaled1e4 =
        "9000"
    ; scaledDecimalStrictGreaterThanPrimitive =
        "Constructed Agda Nat witness for scaled-decimal strict inequality 9566 > 9000, i.e. 0.9566 > 0.90"
    ; scaledDecimalStrictGreaterThanWitness =
        scaledDecimalStrictGreaterThan9566over9000
    ; computedPassBoolean =
        true
    ; computedPassBooleanIsTrue =
        refl
    ; constructsW4ZAdequacy =
        false
    ; constructsW4ZAdequacyIsFalse =
        refl
    ; constructsW4GateReceipt =
        false
    ; constructsW4GateReceiptIsFalse =
        refl
    ; evidenceBoundary =
        "Computed internal adequacy evidence only: 76-106 GeV geometric-mean diagonal efficiency is recorded as 0.9566"
        ∷ "The adequacy bound is recorded as 0.90 using the same string/scaled-decimal convention"
        ∷ "An Agda Nat strict-inequality witness for 9566 > 9000 is constructed here"
        ∷ "This receipt does not construct W4ZAdequacy, accepted DY authority, or a W4 gate receipt"
        ∷ []
    }

canonicalW4ZInternalAdequacyEvidenceDoesNotPromoteW4 :
  W4ZInternalAdequacyEvidenceReceipt.constructsW4GateReceipt
    canonicalW4ZInternalAdequacyEvidenceReceipt
  ≡ false
canonicalW4ZInternalAdequacyEvidenceDoesNotPromoteW4 =
  W4ZInternalAdequacyEvidenceReceipt.constructsW4GateReceiptIsFalse
    canonicalW4ZInternalAdequacyEvidenceReceipt
