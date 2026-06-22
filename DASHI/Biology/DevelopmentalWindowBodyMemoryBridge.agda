module DASHI.Biology.DevelopmentalWindowBodyMemoryBridge where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Biology.BodyKeepsScoreResidualBridge as BodyResidual
import DASHI.Biology.GenomeSensorimotorConnectomeBridge as Genome
import DASHI.Biology.TraumaClinicalGovernanceBoundary as Governance

------------------------------------------------------------------------
-- Developmental windows / body-memory bridge.
--
-- This module tracks candidate-only developmental windows across body-memory
-- residual placement while keeping the hard gates explicit:
--
-- - critical-period determinism is blocked,
-- - DNA is not destiny,
-- - connectome closure is blocked,
-- - trauma proof is blocked,
-- - diagnosis and treatment are blocked,
-- - clinical authority is blocked.
------------------------------------------------------------------------

data Never : Set where

data DevelopmentalWindow : Set where
  prenatalWindow : DevelopmentalWindow
  infancyWindow : DevelopmentalWindow
  childhoodWindow : DevelopmentalWindow
  adolescenceWindow : DevelopmentalWindow
  adulthoodWindow : DevelopmentalWindow
  ageingWindow : DevelopmentalWindow

canonicalDevelopmentalWindows :
  List DevelopmentalWindow
canonicalDevelopmentalWindows =
  prenatalWindow
  ∷ infancyWindow
  ∷ childhoodWindow
  ∷ adolescenceWindow
  ∷ adulthoodWindow
  ∷ ageingWindow
  ∷ []

data DevelopmentalProxyKind : Set where
  plasticityProxyKind : DevelopmentalProxyKind
  pruningProxyKind : DevelopmentalProxyKind
  sensitivePeriodProxyKind : DevelopmentalProxyKind
  residualPlacementProxyKind : DevelopmentalProxyKind

canonicalDevelopmentalProxyKinds :
  List DevelopmentalProxyKind
canonicalDevelopmentalProxyKinds =
  plasticityProxyKind
  ∷ pruningProxyKind
  ∷ sensitivePeriodProxyKind
  ∷ residualPlacementProxyKind
  ∷ []

data BodyMemoryResidualPlacement : Set where
  somaticResidualPlacement : BodyMemoryResidualPlacement
  autonomicResidualPlacement : BodyMemoryResidualPlacement
  interoceptiveResidualPlacement : BodyMemoryResidualPlacement
  affectResidualPlacement : BodyMemoryResidualPlacement
  motorResidualPlacement : BodyMemoryResidualPlacement
  relationalResidualPlacement : BodyMemoryResidualPlacement
  agencyResidualPlacement : BodyMemoryResidualPlacement
  memoryResidualPlacement : BodyMemoryResidualPlacement
  contextualResidualPlacement : BodyMemoryResidualPlacement

canonicalBodyMemoryResidualPlacements :
  List BodyMemoryResidualPlacement
canonicalBodyMemoryResidualPlacements =
  somaticResidualPlacement
  ∷ autonomicResidualPlacement
  ∷ interoceptiveResidualPlacement
  ∷ affectResidualPlacement
  ∷ motorResidualPlacement
  ∷ relationalResidualPlacement
  ∷ agencyResidualPlacement
  ∷ memoryResidualPlacement
  ∷ contextualResidualPlacement
  ∷ []

data DevelopmentalWindowBoundary : Set where
  candidateDevelopmentalContextBoundary : DevelopmentalWindowBoundary
  developmentalWindowBoundary : DevelopmentalWindowBoundary
  plasticityProxyBoundary : DevelopmentalWindowBoundary
  pruningProxyBoundary : DevelopmentalWindowBoundary
  sensitivePeriodProxyBoundary : DevelopmentalWindowBoundary
  bodyMemoryPlacementBoundary : DevelopmentalWindowBoundary
  noCriticalPeriodDeterminismBoundary : DevelopmentalWindowBoundary
  noDNADestinyBoundary : DevelopmentalWindowBoundary
  noConnectomeClosureBoundary : DevelopmentalWindowBoundary
  noTraumaProofBoundary : DevelopmentalWindowBoundary
  noDiagnosisBoundary : DevelopmentalWindowBoundary
  noTreatmentBoundary : DevelopmentalWindowBoundary
  noClinicalAuthorityBoundary : DevelopmentalWindowBoundary

canonicalDevelopmentalWindowBoundaries :
  List DevelopmentalWindowBoundary
canonicalDevelopmentalWindowBoundaries =
  candidateDevelopmentalContextBoundary
  ∷ developmentalWindowBoundary
  ∷ plasticityProxyBoundary
  ∷ pruningProxyBoundary
  ∷ sensitivePeriodProxyBoundary
  ∷ bodyMemoryPlacementBoundary
  ∷ noCriticalPeriodDeterminismBoundary
  ∷ noDNADestinyBoundary
  ∷ noConnectomeClosureBoundary
  ∷ noTraumaProofBoundary
  ∷ noDiagnosisBoundary
  ∷ noTreatmentBoundary
  ∷ noClinicalAuthorityBoundary
  ∷ []

data DevelopmentalWindowRoute : Set where
  candidateDevelopmentalContextRoute : DevelopmentalWindowRoute
  criticalPeriodDeterminismRoute : DevelopmentalWindowRoute
  dnaDestinyRoute : DevelopmentalWindowRoute
  connectomeClosureRoute : DevelopmentalWindowRoute
  traumaProofRoute : DevelopmentalWindowRoute
  diagnosisRoute : DevelopmentalWindowRoute
  treatmentRoute : DevelopmentalWindowRoute
  clinicalAuthorityRoute : DevelopmentalWindowRoute

AdmissibleDevelopmentalWindowRoute :
  DevelopmentalWindowRoute →
  Set
AdmissibleDevelopmentalWindowRoute candidateDevelopmentalContextRoute = ⊤
AdmissibleDevelopmentalWindowRoute criticalPeriodDeterminismRoute = Never
AdmissibleDevelopmentalWindowRoute dnaDestinyRoute = Never
AdmissibleDevelopmentalWindowRoute connectomeClosureRoute = Never
AdmissibleDevelopmentalWindowRoute traumaProofRoute = Never
AdmissibleDevelopmentalWindowRoute diagnosisRoute = Never
AdmissibleDevelopmentalWindowRoute treatmentRoute = Never
AdmissibleDevelopmentalWindowRoute clinicalAuthorityRoute = Never

criticalPeriodDeterminismRejected :
  AdmissibleDevelopmentalWindowRoute criticalPeriodDeterminismRoute →
  Never
criticalPeriodDeterminismRejected impossible =
  impossible

dnaDestinyRejected :
  AdmissibleDevelopmentalWindowRoute dnaDestinyRoute →
  Never
dnaDestinyRejected impossible =
  impossible

connectomeClosureRejected :
  AdmissibleDevelopmentalWindowRoute connectomeClosureRoute →
  Never
connectomeClosureRejected impossible =
  impossible

traumaProofRejected :
  AdmissibleDevelopmentalWindowRoute traumaProofRoute →
  Never
traumaProofRejected impossible =
  impossible

diagnosisRejected :
  AdmissibleDevelopmentalWindowRoute diagnosisRoute →
  Never
diagnosisRejected impossible =
  impossible

treatmentRejected :
  AdmissibleDevelopmentalWindowRoute treatmentRoute →
  Never
treatmentRejected impossible =
  impossible

clinicalAuthorityRejected :
  AdmissibleDevelopmentalWindowRoute clinicalAuthorityRoute →
  Never
clinicalAuthorityRejected impossible =
  impossible

record DevelopmentalWindowBodyMemoryRow : Set where
  constructor mkDevelopmentalWindowBodyMemoryRow
  field
    rowIndex : Nat
    rowWindow : DevelopmentalWindow
    rowProxyKind : DevelopmentalProxyKind
    rowResidualPlacement : BodyMemoryResidualPlacement
    rowLabel : String
    rowClaim : String
    rowCandidateContext : Bool
    rowCandidateContextIsTrue : rowCandidateContext ≡ true
    rowCriticalPeriodDeterminismClaim : Bool
    rowCriticalPeriodDeterminismClaimIsFalse :
      rowCriticalPeriodDeterminismClaim ≡ false
    rowDNADestinyClaim : Bool
    rowDNADestinyClaimIsFalse : rowDNADestinyClaim ≡ false
    rowConnectomeClosureClaim : Bool
    rowConnectomeClosureClaimIsFalse :
      rowConnectomeClosureClaim ≡ false
    rowTraumaProofClaim : Bool
    rowTraumaProofClaimIsFalse : rowTraumaProofClaim ≡ false
    rowDiagnosisClaim : Bool
    rowDiagnosisClaimIsFalse : rowDiagnosisClaim ≡ false
    rowTreatmentClaim : Bool
    rowTreatmentClaimIsFalse : rowTreatmentClaim ≡ false
    rowClinicalAuthorityClaim : Bool
    rowClinicalAuthorityClaimIsFalse :
      rowClinicalAuthorityClaim ≡ false
    rowNotes : List String

open DevelopmentalWindowBodyMemoryRow public

prenatalWindowRow : DevelopmentalWindowBodyMemoryRow
prenatalWindowRow =
  mkDevelopmentalWindowBodyMemoryRow
    zero
    prenatalWindow
    sensitivePeriodProxyKind
    somaticResidualPlacement
    "prenatal window"
    "prenatal development is tracked as a candidate developmental context, not as destiny"
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    ( "sensitive-period proxy row"
    ∷ "body-memory placement remains candidate-only"
    ∷ "no trauma proof, diagnosis, treatment, or clinical authority"
    ∷ []
    )

infancyWindowRow : DevelopmentalWindowBodyMemoryRow
infancyWindowRow =
  mkDevelopmentalWindowBodyMemoryRow
    (suc zero)
    infancyWindow
    plasticityProxyKind
    autonomicResidualPlacement
    "infancy window"
    "infancy development is tracked as a plasticity proxy row, not as causal closure"
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    ( "plasticity proxy row"
    ∷ "body-memory residual placement remains candidate-only"
    ∷ "no diagnosis, treatment, or clinical authority"
    ∷ []
    )

childhoodWindowRow : DevelopmentalWindowBodyMemoryRow
childhoodWindowRow =
  mkDevelopmentalWindowBodyMemoryRow
    (suc (suc zero))
    childhoodWindow
    pruningProxyKind
    interoceptiveResidualPlacement
    "childhood window"
    "childhood development is tracked as a pruning proxy row, not as connectome closure"
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    ( "pruning proxy row"
    ∷ "body-memory placement remains candidate-only"
    ∷ "no connectome closure, trauma proof, or diagnosis"
    ∷ []
    )

adolescenceWindowRow : DevelopmentalWindowBodyMemoryRow
adolescenceWindowRow =
  mkDevelopmentalWindowBodyMemoryRow
    (suc (suc (suc zero)))
    adolescenceWindow
    plasticityProxyKind
    affectResidualPlacement
    "adolescence window"
    "adolescence development is tracked as a plasticity proxy row, not as deterministic fate"
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    ( "plasticity proxy row"
    ∷ "body-memory residual placement remains candidate-only"
    ∷ "no destiny, diagnosis, treatment, or clinical authority"
    ∷ []
    )

adulthoodWindowRow : DevelopmentalWindowBodyMemoryRow
adulthoodWindowRow =
  mkDevelopmentalWindowBodyMemoryRow
    (suc (suc (suc (suc zero))))
    adulthoodWindow
    residualPlacementProxyKind
    relationalResidualPlacement
    "adulthood window"
    "adulthood development is tracked as a residual-placement proxy row, not as clinical authority"
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    ( "residual-placement proxy row"
    ∷ "body-memory placement remains candidate-only"
    ∷ "no clinical authority or treatment authority"
    ∷ []
    )

ageingWindowRow : DevelopmentalWindowBodyMemoryRow
ageingWindowRow =
  mkDevelopmentalWindowBodyMemoryRow
    (suc (suc (suc (suc (suc zero)))))
    ageingWindow
    residualPlacementProxyKind
    memoryResidualPlacement
    "ageing window"
    "ageing development is tracked as a retention proxy row, not as diagnosis or cure"
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    ( "retention proxy row"
    ∷ "body-memory residual placement remains candidate-only"
    ∷ "no trauma proof, diagnosis, treatment, or clinical authority"
    ∷ []
    )

canonicalDevelopmentalWindowBodyMemoryRows :
  List DevelopmentalWindowBodyMemoryRow
canonicalDevelopmentalWindowBodyMemoryRows =
  prenatalWindowRow
  ∷ infancyWindowRow
  ∷ childhoodWindowRow
  ∷ adolescenceWindowRow
  ∷ adulthoodWindowRow
  ∷ ageingWindowRow
  ∷ []

record DevelopmentalWindowBodyMemoryBridge : Setω where
  field
    genomeSensorimotorBridge :
      Genome.GenomeSensorimotorConnectomeBridge

    genomeSensorimotorBridgeIsCanonical :
      Bool

    bodyMemoryResidualBridge :
      BodyResidual.BodyKeepsScoreResidualBridge

    bodyMemoryResidualBridgeIsCanonical :
      Bool

    traumaClinicalGovernanceBoundary :
      Governance.TraumaClinicalGovernanceBoundary

    traumaClinicalGovernanceBoundaryIsCanonical :
      Bool

    windows :
      List DevelopmentalWindow

    windowsAreCanonical :
      windows ≡ canonicalDevelopmentalWindows

    proxyKinds :
      List DevelopmentalProxyKind

    proxyKindsAreCanonical :
      proxyKinds ≡ canonicalDevelopmentalProxyKinds

    residualPlacements :
      List BodyMemoryResidualPlacement

    residualPlacementsAreCanonical :
      residualPlacements ≡ canonicalBodyMemoryResidualPlacements

    rows :
      List DevelopmentalWindowBodyMemoryRow

    rowsAreCanonical :
      rows ≡ canonicalDevelopmentalWindowBodyMemoryRows

    boundaries :
      List DevelopmentalWindowBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalDevelopmentalWindowBoundaries

    route :
      DevelopmentalWindowRoute

    routeIsCandidateDevelopmentalContext :
      route ≡ candidateDevelopmentalContextRoute

    routeAdmissible :
      AdmissibleDevelopmentalWindowRoute route

    candidateDevelopmentalContext :
      Bool

    candidateDevelopmentalContextIsTrue :
      candidateDevelopmentalContext ≡ true

    criticalPeriodDeterminismClaim :
      Bool

    criticalPeriodDeterminismClaimIsFalse :
      criticalPeriodDeterminismClaim ≡ false

    dnaDestinyClaim :
      Bool

    dnaDestinyClaimIsFalse :
      dnaDestinyClaim ≡ false

    connectomeClosureClaim :
      Bool

    connectomeClosureClaimIsFalse :
      connectomeClosureClaim ≡ false

    traumaProofClaim :
      Bool

    traumaProofClaimIsFalse :
      traumaProofClaim ≡ false

    diagnosisClaim :
      Bool

    diagnosisClaimIsFalse :
      diagnosisClaim ≡ false

    treatmentClaim :
      Bool

    treatmentClaimIsFalse :
      treatmentClaim ≡ false

    clinicalAuthorityClaim :
      Bool

    clinicalAuthorityClaimIsFalse :
      clinicalAuthorityClaim ≡ false

    bridgeReading :
      String

open DevelopmentalWindowBodyMemoryBridge public

record DevelopmentalWindowBodyMemoryCertificate
    (bridge : DevelopmentalWindowBodyMemoryBridge) : Set where
  field
    routeHeld :
      route bridge ≡ candidateDevelopmentalContextRoute

    candidateDevelopmentalContextHeld :
      candidateDevelopmentalContext bridge ≡ true

    criticalPeriodDeterminismBlocked :
      criticalPeriodDeterminismClaim bridge ≡ false

    dnaDestinyBlocked :
      dnaDestinyClaim bridge ≡ false

    connectomeClosureBlocked :
      connectomeClosureClaim bridge ≡ false

    traumaProofBlocked :
      traumaProofClaim bridge ≡ false

    diagnosisBlocked :
      diagnosisClaim bridge ≡ false

    treatmentBlocked :
      treatmentClaim bridge ≡ false

    clinicalAuthorityBlocked :
      clinicalAuthorityClaim bridge ≡ false

    certificateReading :
      String

open DevelopmentalWindowBodyMemoryCertificate public

canonicalDevelopmentalWindowBodyMemoryBridge :
  DevelopmentalWindowBodyMemoryBridge
canonicalDevelopmentalWindowBodyMemoryBridge =
  record
    { genomeSensorimotorBridge =
        Genome.canonicalGenomeSensorimotorConnectomeBridge
    ; genomeSensorimotorBridgeIsCanonical =
        true
    ; bodyMemoryResidualBridge =
        BodyResidual.canonicalBodyKeepsScoreResidualBridge
    ; bodyMemoryResidualBridgeIsCanonical =
        true
    ; traumaClinicalGovernanceBoundary =
        Governance.canonicalTraumaClinicalGovernanceBoundary
    ; traumaClinicalGovernanceBoundaryIsCanonical =
        true
    ; windows =
        canonicalDevelopmentalWindows
    ; windowsAreCanonical =
        refl
    ; proxyKinds =
        canonicalDevelopmentalProxyKinds
    ; proxyKindsAreCanonical =
        refl
    ; residualPlacements =
        canonicalBodyMemoryResidualPlacements
    ; residualPlacementsAreCanonical =
        refl
    ; rows =
        canonicalDevelopmentalWindowBodyMemoryRows
    ; rowsAreCanonical =
        refl
    ; boundaries =
        canonicalDevelopmentalWindowBoundaries
    ; boundariesAreCanonical =
        refl
    ; route =
        candidateDevelopmentalContextRoute
    ; routeIsCandidateDevelopmentalContext =
        refl
    ; routeAdmissible =
        tt
    ; candidateDevelopmentalContext =
        true
    ; candidateDevelopmentalContextIsTrue =
        refl
    ; criticalPeriodDeterminismClaim =
        false
    ; criticalPeriodDeterminismClaimIsFalse =
        refl
    ; dnaDestinyClaim =
        false
    ; dnaDestinyClaimIsFalse =
        refl
    ; connectomeClosureClaim =
        false
    ; connectomeClosureClaimIsFalse =
        refl
    ; traumaProofClaim =
        false
    ; traumaProofClaimIsFalse =
        refl
    ; diagnosisClaim =
        false
    ; diagnosisClaimIsFalse =
        refl
    ; treatmentClaim =
        false
    ; treatmentClaimIsFalse =
        refl
    ; clinicalAuthorityClaim =
        false
    ; clinicalAuthorityClaimIsFalse =
        refl
    ; bridgeReading =
        "Developmental windows shape candidate-only body-memory placement across prenatal, infancy, childhood, adolescence, adulthood, and ageing contexts; the bridge blocks critical-period determinism, DNA destiny, connectome closure, trauma proof, diagnosis, treatment, and clinical authority."
    }

canonicalDevelopmentalWindowBodyMemoryCertificate :
  DevelopmentalWindowBodyMemoryCertificate
    canonicalDevelopmentalWindowBodyMemoryBridge
canonicalDevelopmentalWindowBodyMemoryCertificate =
  record
    { routeHeld =
        refl
    ; candidateDevelopmentalContextHeld =
        refl
    ; criticalPeriodDeterminismBlocked =
        refl
    ; dnaDestinyBlocked =
        refl
    ; connectomeClosureBlocked =
        refl
    ; traumaProofBlocked =
        refl
    ; diagnosisBlocked =
        refl
    ; treatmentBlocked =
        refl
    ; clinicalAuthorityBlocked =
        refl
    ; certificateReading =
        "The developmental-window bridge remains candidate-only and fail-closed."
    }

------------------------------------------------------------------------
-- Canonical boundary lemmas.
------------------------------------------------------------------------

canonicalRouteIsCandidateDevelopmentalContext :
  route canonicalDevelopmentalWindowBodyMemoryBridge
  ≡
  candidateDevelopmentalContextRoute
canonicalRouteIsCandidateDevelopmentalContext =
  routeIsCandidateDevelopmentalContext
    canonicalDevelopmentalWindowBodyMemoryBridge

canonicalCandidateDevelopmentalContextIsTrue :
  candidateDevelopmentalContext
    canonicalDevelopmentalWindowBodyMemoryBridge
  ≡
  true
canonicalCandidateDevelopmentalContextIsTrue =
  candidateDevelopmentalContextIsTrue
    canonicalDevelopmentalWindowBodyMemoryBridge

canonicalCriticalPeriodDeterminismClaimIsFalse :
  criticalPeriodDeterminismClaim
    canonicalDevelopmentalWindowBodyMemoryBridge
  ≡
  false
canonicalCriticalPeriodDeterminismClaimIsFalse =
  criticalPeriodDeterminismClaimIsFalse
    canonicalDevelopmentalWindowBodyMemoryBridge

canonicalDnaDestinyClaimIsFalse :
  dnaDestinyClaim canonicalDevelopmentalWindowBodyMemoryBridge ≡ false
canonicalDnaDestinyClaimIsFalse =
  dnaDestinyClaimIsFalse canonicalDevelopmentalWindowBodyMemoryBridge

canonicalConnectomeClosureClaimIsFalse :
  connectomeClosureClaim canonicalDevelopmentalWindowBodyMemoryBridge
  ≡
  false
canonicalConnectomeClosureClaimIsFalse =
  connectomeClosureClaimIsFalse canonicalDevelopmentalWindowBodyMemoryBridge

canonicalTraumaProofClaimIsFalse :
  traumaProofClaim canonicalDevelopmentalWindowBodyMemoryBridge ≡ false
canonicalTraumaProofClaimIsFalse =
  traumaProofClaimIsFalse canonicalDevelopmentalWindowBodyMemoryBridge

canonicalDiagnosisClaimIsFalse :
  diagnosisClaim canonicalDevelopmentalWindowBodyMemoryBridge ≡ false
canonicalDiagnosisClaimIsFalse =
  diagnosisClaimIsFalse canonicalDevelopmentalWindowBodyMemoryBridge

canonicalTreatmentClaimIsFalse :
  treatmentClaim canonicalDevelopmentalWindowBodyMemoryBridge ≡ false
canonicalTreatmentClaimIsFalse =
  treatmentClaimIsFalse canonicalDevelopmentalWindowBodyMemoryBridge

canonicalClinicalAuthorityClaimIsFalse :
  clinicalAuthorityClaim canonicalDevelopmentalWindowBodyMemoryBridge
  ≡
  false
canonicalClinicalAuthorityClaimIsFalse =
  clinicalAuthorityClaimIsFalse canonicalDevelopmentalWindowBodyMemoryBridge

canonicalWindowsAreCanonical :
  windows canonicalDevelopmentalWindowBodyMemoryBridge
  ≡
  canonicalDevelopmentalWindows
canonicalWindowsAreCanonical =
  windowsAreCanonical canonicalDevelopmentalWindowBodyMemoryBridge

canonicalProxyKindsAreCanonical :
  proxyKinds canonicalDevelopmentalWindowBodyMemoryBridge
  ≡
  canonicalDevelopmentalProxyKinds
canonicalProxyKindsAreCanonical =
  proxyKindsAreCanonical canonicalDevelopmentalWindowBodyMemoryBridge

canonicalResidualPlacementsAreCanonical :
  residualPlacements canonicalDevelopmentalWindowBodyMemoryBridge
  ≡
  canonicalBodyMemoryResidualPlacements
canonicalResidualPlacementsAreCanonical =
  residualPlacementsAreCanonical canonicalDevelopmentalWindowBodyMemoryBridge

canonicalRowsAreCanonical :
  rows canonicalDevelopmentalWindowBodyMemoryBridge
  ≡
  canonicalDevelopmentalWindowBodyMemoryRows
canonicalRowsAreCanonical =
  rowsAreCanonical canonicalDevelopmentalWindowBodyMemoryBridge

canonicalBoundariesAreCanonical :
  boundaries canonicalDevelopmentalWindowBodyMemoryBridge
  ≡
  canonicalDevelopmentalWindowBoundaries
canonicalBoundariesAreCanonical =
  boundariesAreCanonical canonicalDevelopmentalWindowBodyMemoryBridge
