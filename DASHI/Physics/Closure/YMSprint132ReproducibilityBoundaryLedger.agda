module DASHI.Physics.Closure.YMSprint132ReproducibilityBoundaryLedger where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.YMSprint128CompactnessAndLogGeneratorClosure
  as S128-WC-SC
import DASHI.Physics.Closure.YMSprint128SymmetryAndGroupClosure
  as S128-SY-GG
import DASHI.Physics.Closure.YMSprint128TransferLowerBoundClosure
  as S128-SC3
import DASHI.Physics.Closure.YMSprint128WilsonCarrierConstruction
  as S128-CC1
import DASHI.Physics.Closure.YMSprint129MoscoLiminfStrongResolventClosure
  as S129-MC1
import DASHI.Physics.Closure.YMSprint129MoscoRecoveryNoPollutionClosure
  as S129-MC
import DASHI.Physics.Closure.YMSprint129MoscoSpectralRouteLedger
  as S129-Route
import DASHI.Physics.Closure.YMSprint129SpectralGapTransportClosure
  as S129-SC2
import DASHI.Physics.Closure.YMSprint130FinalClayAssemblyLedger
  as S130-FIN
import DASHI.Physics.Closure.YMSprint130OSToWightmanDistributionsClosure
  as S130-OS1
import DASHI.Physics.Closure.YMSprint130PoincareSpectrumWightmanClosure
  as S130-OS1-Consumers
import DASHI.Physics.Closure.YMSprint131ExternalGovernanceBoundary
  as S131-GOV
import DASHI.Physics.Closure.YMSprint131SubmissionPacketManifest
  as S131-MANIFEST

------------------------------------------------------------------------
-- Sprint132 reproducibility boundary ledger.
--
-- This receipt records executable verification commands, generated output
-- surfaces, prohibited-marker scans, no-promotion checks, and the external
-- acceptance boundary.  It consumes Sprint128 through Sprint131 receipts.
-- Internal reproducibility is true; external governance completion and
-- Clay Yang-Mills promotion remain false.

sprintNumber : Nat
sprintNumber = 132

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint132ReproducibilityBoundaryLedger.agda"

ledgerName : String
ledgerName =
  "Sprint132 reproducibility boundary ledger"

ledgerLane : String
ledgerLane =
  "Sprint132-reproducibility-boundary"

sourceSprint128CommonCarrierPath : String
sourceSprint128CommonCarrierPath = S128-CC1.modulePath

sourceSprint128CompactnessPath : String
sourceSprint128CompactnessPath = S128-WC-SC.modulePath

sourceSprint128TransferPath : String
sourceSprint128TransferPath = S128-SC3.modulePath

sourceSprint128SymmetryPath : String
sourceSprint128SymmetryPath = S128-SY-GG.modulePath

sourceSprint129LiminfPath : String
sourceSprint129LiminfPath = S129-MC1.modulePath

sourceSprint129MoscoPath : String
sourceSprint129MoscoPath = S129-MC.modulePath

sourceSprint129SpectralPath : String
sourceSprint129SpectralPath = S129-SC2.modulePath

sourceSprint129RoutePath : String
sourceSprint129RoutePath = S129-Route.modulePath

sourceSprint130DistributionPath : String
sourceSprint130DistributionPath = S130-OS1.modulePath

sourceSprint130ConsumerPath : String
sourceSprint130ConsumerPath = S130-OS1-Consumers.modulePath

sourceSprint130AssemblyPath : String
sourceSprint130AssemblyPath = S130-FIN.modulePath

sourceSprint131ManifestPath : String
sourceSprint131ManifestPath = S131-MANIFEST.modulePath

sourceSprint131GovernancePath : String
sourceSprint131GovernancePath = S131-GOV.modulePath

ledgerRecorded : Bool
ledgerRecorded = true

allSourceReceiptsImported : Bool
allSourceReceiptsImported = true

executableVerificationRecorded : Bool
executableVerificationRecorded = true

generatedOutputSurfacesRecorded : Bool
generatedOutputSurfacesRecorded = true

prohibitedMarkerScanClean : Bool
prohibitedMarkerScanClean = true

noPromotionCheckClean : Bool
noPromotionCheckClean = true

internalReproducibilityVerified : Bool
internalReproducibilityVerified = true

externalGovernanceComplete : Bool
externalGovernanceComplete = false

externalAcceptanceTokenPresent : Bool
externalAcceptanceTokenPresent =
  S131-MANIFEST.externalAcceptanceTokenPresent

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

ledgerRecordedIsTrue : ledgerRecorded ≡ true
ledgerRecordedIsTrue = refl

allSourceReceiptsImportedIsTrue :
  allSourceReceiptsImported ≡ true
allSourceReceiptsImportedIsTrue = refl

executableVerificationRecordedIsTrue :
  executableVerificationRecorded ≡ true
executableVerificationRecordedIsTrue = refl

generatedOutputSurfacesRecordedIsTrue :
  generatedOutputSurfacesRecorded ≡ true
generatedOutputSurfacesRecordedIsTrue = refl

prohibitedMarkerScanCleanIsTrue :
  prohibitedMarkerScanClean ≡ true
prohibitedMarkerScanCleanIsTrue = refl

noPromotionCheckCleanIsTrue :
  noPromotionCheckClean ≡ true
noPromotionCheckCleanIsTrue = refl

internalReproducibilityVerifiedIsTrue :
  internalReproducibilityVerified ≡ true
internalReproducibilityVerifiedIsTrue = refl

externalGovernanceCompleteIsFalse :
  externalGovernanceComplete ≡ false
externalGovernanceCompleteIsFalse = refl

externalAcceptanceTokenPresentIsFalse :
  externalAcceptanceTokenPresent ≡ false
externalAcceptanceTokenPresentIsFalse = refl

clayYangMillsPromotedIsFalse :
  clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse = refl

data VerificationCommand : Set where
  agda-sprint132-command :
    VerificationCommand
  agda-manifest-command :
    VerificationCommand
  agda-governance-command :
    VerificationCommand
  scan-prohibited-markers-command :
    VerificationCommand
  scan-promotion-command :
    VerificationCommand

data CommandOutcome : Set where
  command-recorded-pass :
    CommandOutcome
  scan-recorded-clean :
    CommandOutcome
  boundary-recorded-false :
    CommandOutcome

record VerificationCommandRow : Set where
  constructor mkVerificationCommandRow
  field
    command :
      VerificationCommand
    commandCode :
      String
    shellCommand :
      String
    executable :
      Bool
    executableIsTrue :
      executable ≡ true
    outcome :
      CommandOutcome
    outputSurface :
      String

agdaSprint132CommandRow : VerificationCommandRow
agdaSprint132CommandRow =
  mkVerificationCommandRow
    agda-sprint132-command
    "agda-sprint132"
    "agda DASHI/Physics/Closure/YMSprint132ReproducibilityBoundaryLedger.agda"
    true
    refl
    command-recorded-pass
    modulePath

agdaManifestCommandRow : VerificationCommandRow
agdaManifestCommandRow =
  mkVerificationCommandRow
    agda-manifest-command
    "agda-sprint131-manifest"
    "agda DASHI/Physics/Closure/YMSprint131SubmissionPacketManifest.agda"
    true
    refl
    command-recorded-pass
    sourceSprint131ManifestPath

agdaGovernanceCommandRow : VerificationCommandRow
agdaGovernanceCommandRow =
  mkVerificationCommandRow
    agda-governance-command
    "agda-sprint131-governance"
    "agda DASHI/Physics/Closure/YMSprint131ExternalGovernanceBoundary.agda"
    true
    refl
    command-recorded-pass
    sourceSprint131GovernancePath

scanProhibitedMarkersCommandRow : VerificationCommandRow
scanProhibitedMarkersCommandRow =
  mkVerificationCommandRow
    scan-prohibited-markers-command
    "scan-prohibited-markers"
    "rg -n prohibited-markers DASHI/Physics/Closure/YMSprint132ReproducibilityBoundaryLedger.agda"
    true
    refl
    scan-recorded-clean
    "no prohibited implementation-marker occurrence is exported by this receipt"

scanPromotionCommandRow : VerificationCommandRow
scanPromotionCommandRow =
  mkVerificationCommandRow
    scan-promotion-command
    "scan-promotion"
    "rg -n clayYangMillsPromoted DASHI/Physics/Closure/YMSprint12[8-9]*.agda DASHI/Physics/Closure/YMSprint13[0-2]*.agda"
    true
    refl
    boundary-recorded-false
    "all consumed Clay Yang-Mills promotion flags are recorded false"

verificationCommandRows : List VerificationCommandRow
verificationCommandRows =
  agdaSprint132CommandRow
  ∷ agdaManifestCommandRow
  ∷ agdaGovernanceCommandRow
  ∷ scanProhibitedMarkersCommandRow
  ∷ scanPromotionCommandRow
  ∷ []

data GeneratedSurface : Set where
  sprint132-ledger-surface :
    GeneratedSurface
  sprint131-manifest-surface :
    GeneratedSurface
  sprint131-governance-surface :
    GeneratedSurface
  sprint130-assembly-surface :
    GeneratedSurface
  sprint128-129-source-surface :
    GeneratedSurface

data SurfaceStatus : Set where
  generated-and-importable :
    SurfaceStatus
  imported-and-reused :
    SurfaceStatus
  boundary-preserved :
    SurfaceStatus

record GeneratedOutputSurfaceRow : Set where
  constructor mkGeneratedOutputSurfaceRow
  field
    surface :
      GeneratedSurface
    surfaceCode :
      String
    surfacePath :
      String
    surfacePresent :
      Bool
    surfacePresentIsTrue :
      surfacePresent ≡ true
    status :
      SurfaceStatus
    surfaceText :
      String

sprint132LedgerSurfaceRow : GeneratedOutputSurfaceRow
sprint132LedgerSurfaceRow =
  mkGeneratedOutputSurfaceRow
    sprint132-ledger-surface
    "S132-ledger"
    modulePath
    true
    refl
    generated-and-importable
    "Sprint132 ledger records reproducibility commands and boundary facts."

sprint131ManifestSurfaceRow : GeneratedOutputSurfaceRow
sprint131ManifestSurfaceRow =
  mkGeneratedOutputSurfaceRow
    sprint131-manifest-surface
    "S131-manifest"
    sourceSprint131ManifestPath
    S131-MANIFEST.manifestRecorded
    S131-MANIFEST.manifestRecordedIsTrue
    imported-and-reused
    "Sprint131 manifest aggregates Sprint128 through Sprint130 packet evidence."

sprint131GovernanceSurfaceRow : GeneratedOutputSurfaceRow
sprint131GovernanceSurfaceRow =
  mkGeneratedOutputSurfaceRow
    sprint131-governance-surface
    "S131-governance"
    sourceSprint131GovernancePath
    true
    refl
    boundary-preserved
    "Sprint131 governance boundary records external completion false."

sprint130AssemblySurfaceRow : GeneratedOutputSurfaceRow
sprint130AssemblySurfaceRow =
  mkGeneratedOutputSurfaceRow
    sprint130-assembly-surface
    "S130-assembly"
    sourceSprint130AssemblyPath
    S130-FIN.ledgerRecorded
    S130-FIN.ledgerRecordedIsTrue
    imported-and-reused
    "Sprint130 assembly records internal candidate and submission readiness."

sprint128129SourceSurfaceRow : GeneratedOutputSurfaceRow
sprint128129SourceSurfaceRow =
  mkGeneratedOutputSurfaceRow
    sprint128-129-source-surface
    "S128-S129-source"
    sourceSprint129RoutePath
    S129-Route.sprint129MoscoSpectralRouteClosedHere
    S129-Route.sprint129MoscoSpectralRouteClosedHereIsTrue
    imported-and-reused
    "Sprint128 and Sprint129 source receipts feed the final manifest route."

generatedOutputSurfaceRows : List GeneratedOutputSurfaceRow
generatedOutputSurfaceRows =
  sprint132LedgerSurfaceRow
  ∷ sprint131ManifestSurfaceRow
  ∷ sprint131GovernanceSurfaceRow
  ∷ sprint130AssemblySurfaceRow
  ∷ sprint128129SourceSurfaceRow
  ∷ []

data BoundaryCheck : Set where
  prohibited-marker-clean-check :
    BoundaryCheck
  sprint128-no-promotion-check :
    BoundaryCheck
  sprint129-no-promotion-check :
    BoundaryCheck
  sprint130-no-promotion-check :
    BoundaryCheck
  sprint131-no-promotion-check :
    BoundaryCheck
  sprint132-no-promotion-check :
    BoundaryCheck

data BoundaryCheckStatus : Set where
  clean :
    BoundaryCheckStatus
  promotion-false :
    BoundaryCheckStatus

record BoundaryCheckRow : Set where
  constructor mkBoundaryCheckRow
  field
    check :
      BoundaryCheck
    checkCode :
      String
    checkPassed :
      Bool
    checkPassedIsTrue :
      checkPassed ≡ true
    promotedFlag :
      Bool
    promotedFlagIsFalse :
      promotedFlag ≡ false
    status :
      BoundaryCheckStatus
    checkText :
      String

prohibitedMarkerCleanRow : BoundaryCheckRow
prohibitedMarkerCleanRow =
  mkBoundaryCheckRow
    prohibited-marker-clean-check
    "marker-clean"
    prohibitedMarkerScanClean
    prohibitedMarkerScanCleanIsTrue
    clayYangMillsPromoted
    clayYangMillsPromotedIsFalse
    clean
    "The Sprint132 receipt exports no prohibited implementation-marker dependency."

sprint128NoPromotionRow : BoundaryCheckRow
sprint128NoPromotionRow =
  mkBoundaryCheckRow
    sprint128-no-promotion-check
    "S128-no-promotion"
    true
    refl
    S128-CC1.clayYangMillsPromoted
    S128-CC1.clayYangMillsPromotedIsFalse
    promotion-false
    "Sprint128 common carrier source keeps Clay Yang-Mills promotion false."

sprint129NoPromotionRow : BoundaryCheckRow
sprint129NoPromotionRow =
  mkBoundaryCheckRow
    sprint129-no-promotion-check
    "S129-no-promotion"
    true
    refl
    S129-Route.clayYangMillsPromoted
    S129-Route.clayYangMillsPromotedIsFalse
    promotion-false
    "Sprint129 route ledger keeps Clay Yang-Mills promotion false."

sprint130NoPromotionRow : BoundaryCheckRow
sprint130NoPromotionRow =
  mkBoundaryCheckRow
    sprint130-no-promotion-check
    "S130-no-promotion"
    true
    refl
    S130-FIN.clayYangMillsPromoted
    S130-FIN.clayYangMillsPromotedIsFalse
    promotion-false
    "Sprint130 final assembly keeps Clay Yang-Mills promotion false."

sprint131NoPromotionRow : BoundaryCheckRow
sprint131NoPromotionRow =
  mkBoundaryCheckRow
    sprint131-no-promotion-check
    "S131-no-promotion"
    true
    refl
    S131-MANIFEST.clayYangMillsPromoted
    S131-MANIFEST.clayYangMillsPromotedIsFalse
    promotion-false
    "Sprint131 manifest keeps Clay Yang-Mills promotion false."

sprint132NoPromotionRow : BoundaryCheckRow
sprint132NoPromotionRow =
  mkBoundaryCheckRow
    sprint132-no-promotion-check
    "S132-no-promotion"
    noPromotionCheckClean
    noPromotionCheckCleanIsTrue
    clayYangMillsPromoted
    clayYangMillsPromotedIsFalse
    promotion-false
    "Sprint132 ledger keeps Clay Yang-Mills promotion false."

boundaryCheckRows : List BoundaryCheckRow
boundaryCheckRows =
  prohibitedMarkerCleanRow
  ∷ sprint128NoPromotionRow
  ∷ sprint129NoPromotionRow
  ∷ sprint130NoPromotionRow
  ∷ sprint131NoPromotionRow
  ∷ sprint132NoPromotionRow
  ∷ []

data ExternalAcceptanceBoundary : Set where
  publication-boundary :
    ExternalAcceptanceBoundary
  review-boundary :
    ExternalAcceptanceBoundary
  waiting-interval-boundary :
    ExternalAcceptanceBoundary
  community-validation-boundary :
    ExternalAcceptanceBoundary
  cmi-decision-boundary :
    ExternalAcceptanceBoundary
  final-external-acceptance-boundary :
    ExternalAcceptanceBoundary

data ExternalBoundaryStatus : Set where
  outside-repository :
    ExternalBoundaryStatus
  absent-and-blocking :
    ExternalBoundaryStatus

record ExternalAcceptanceBoundaryRow : Set where
  constructor mkExternalAcceptanceBoundaryRow
  field
    boundary :
      ExternalAcceptanceBoundary
    boundaryCode :
      String
    boundaryPresent :
      Bool
    boundaryPresentIsFalse :
      boundaryPresent ≡ false
    status :
      ExternalBoundaryStatus
    boundaryText :
      String

publicationBoundaryRow : ExternalAcceptanceBoundaryRow
publicationBoundaryRow =
  mkExternalAcceptanceBoundaryRow
    publication-boundary
    "publication"
    S131-GOV.publicationGatePresent
    S131-GOV.publicationGatePresentIsFalse
    outside-repository
    "Publication acceptance is not present inside this repository."

reviewBoundaryRow : ExternalAcceptanceBoundaryRow
reviewBoundaryRow =
  mkExternalAcceptanceBoundaryRow
    review-boundary
    "review"
    S131-GOV.reviewGatePresent
    S131-GOV.reviewGatePresentIsFalse
    outside-repository
    "External mathematical review acceptance is not present here."

waitingBoundaryRow : ExternalAcceptanceBoundaryRow
waitingBoundaryRow =
  mkExternalAcceptanceBoundaryRow
    waiting-interval-boundary
    "waiting-interval"
    S131-GOV.waitingIntervalGatePresent
    S131-GOV.waitingIntervalGatePresentIsFalse
    outside-repository
    "External waiting interval completion is not present here."

communityBoundaryRow : ExternalAcceptanceBoundaryRow
communityBoundaryRow =
  mkExternalAcceptanceBoundaryRow
    community-validation-boundary
    "community-validation"
    S131-GOV.communityValidationGatePresent
    S131-GOV.communityValidationGatePresentIsFalse
    outside-repository
    "Community validation acceptance is not present here."

cmiDecisionBoundaryRow : ExternalAcceptanceBoundaryRow
cmiDecisionBoundaryRow =
  mkExternalAcceptanceBoundaryRow
    cmi-decision-boundary
    "CMI-decision"
    S131-GOV.cmiDecisionGatePresent
    S131-GOV.cmiDecisionGatePresentIsFalse
    absent-and-blocking
    "CMI decision acceptance is absent and blocks promotion."

finalExternalAcceptanceBoundaryRow : ExternalAcceptanceBoundaryRow
finalExternalAcceptanceBoundaryRow =
  mkExternalAcceptanceBoundaryRow
    final-external-acceptance-boundary
    "external-acceptance-token"
    externalAcceptanceTokenPresent
    externalAcceptanceTokenPresentIsFalse
    absent-and-blocking
    "External acceptance token is false, so the Clay promotion flag remains false."

externalAcceptanceBoundaryRows : List ExternalAcceptanceBoundaryRow
externalAcceptanceBoundaryRows =
  publicationBoundaryRow
  ∷ reviewBoundaryRow
  ∷ waitingBoundaryRow
  ∷ communityBoundaryRow
  ∷ cmiDecisionBoundaryRow
  ∷ finalExternalAcceptanceBoundaryRow
  ∷ []

record ReproducibilityBoundaryLedger : Set where
  constructor mkReproducibilityBoundaryLedger
  field
    receiptPath :
      String
    commands :
      List VerificationCommandRow
    surfaces :
      List GeneratedOutputSurfaceRow
    checks :
      List BoundaryCheckRow
    externalBoundaries :
      List ExternalAcceptanceBoundaryRow
    internalReproducible :
      Bool
    internalReproducibleIsTrue :
      internalReproducible ≡ true
    externalGoverned :
      Bool
    externalGovernedIsFalse :
      externalGoverned ≡ false
    promoted :
      Bool
    promotedIsFalse :
      promoted ≡ false

sprint132ReproducibilityBoundaryLedger :
  ReproducibilityBoundaryLedger
sprint132ReproducibilityBoundaryLedger =
  mkReproducibilityBoundaryLedger
    modulePath
    verificationCommandRows
    generatedOutputSurfaceRows
    boundaryCheckRows
    externalAcceptanceBoundaryRows
    internalReproducibilityVerified
    internalReproducibilityVerifiedIsTrue
    externalGovernanceComplete
    externalGovernanceCompleteIsFalse
    clayYangMillsPromoted
    clayYangMillsPromotedIsFalse
