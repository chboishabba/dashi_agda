module DASHI.Foundations.UBP.ExactRealBackendBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Rational using (ℚ)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.UBP.ExactRealSourceAtlas as Sources
import DASHI.Foundations.UBP.Pi50ConvergentTable as Pi50

data BackendRole : Set where
  preserveExistingConstructiveAnalysis : BackendRole
  narrowPiYIntervalCertificates : BackendRole
  prototypeGeneralAnalyticBackend : BackendRole

data BackendKind : Set where
  bishopRegularSequences : BackendKind
  rationalEnclosures : BackendKind
  cubicalHoTTReals : BackendKind

record BackendSuitability : Set where
  constructor backendSuitability
  field
    kind : BackendKind
    role : BackendRole
    sourceAuthor : String
    sourceTitle : String
    sourceDOI : String
    implementationURL : String
    currentlyKernelIntegrated : Bool
    suitableForGeneralComposedArithmeticEstablished : Bool
    computationalRiskRecorded : Bool
    reading : String

bishopMigrationBackend : BackendSuitability
bishopMigrationBackend =
  backendSuitability
    bishopRegularSequences
    preserveExistingConstructiveAnalysis
    (Sources.author Sources.murrayBishopReals)
    (Sources.title Sources.murrayBishopReals)
    "10.48550/arXiv.2205.08354"
    (Sources.canonicalURL Sources.csimmaBishopRepository)
    true
    false
    true
    "retain and migrate the existing theorem corpus, but do not infer that regular rational sequences are the optimal backend for deep composed arithmetic"

narrowIntervalBackend : BackendSuitability
narrowIntervalBackend =
  backendSuitability
    rationalEnclosures
    narrowPiYIntervalCertificates
    "DASHI contributors, using attributed continued-fraction data"
    "Narrow rational pi/Y enclosure lane"
    "no external DOI; local certificate architecture"
    "DASHI.Foundations.UBP.Pi50ConvergentTable"
    true
    true
    false
    "use exact rational endpoints and monotone interval transport for the single observer target instead of waiting for a universal executable real field"

cubicalPrototypeBackend : BackendSuitability
cubicalPrototypeBackend =
  backendSuitability
    cubicalHoTTReals
    prototypeGeneralAnalyticBackend
    (Sources.author Sources.broughHoTTReals)
    (Sources.title Sources.broughHoTTReals)
    "10.48550/arXiv.2604.24782"
    (Sources.canonicalURL Sources.broughHoTTReals)
    false
    false
    false
    "prototype against a hard analytic archetype before choosing it; interoperability with non-cubical DASHI and extraction remain explicit obligations"

record KAbsMigrationDecision : Set where
  constructor kAbsMigrationDecision
  field
    inspectActualRationalCarrier : Bool
    inspectActualRationalCarrierIsTrue :
      inspectActualRationalCarrier ≡ true
    assumeNormalisedRationalReflTransfersToCarrier : Bool
    assumeNormalisedRationalReflTransfersToCarrierIsFalse :
      assumeNormalisedRationalReflTransfersToCarrier ≡ false
    testConstructorLevelAbsIdempotenceFirst : Bool
    testConstructorLevelAbsIdempotenceFirstIsTrue :
      testConstructorLevelAbsIdempotenceFirst ≡ true
    deriveKAbsOnlyFromRepresentationEquality : Bool
    deriveKAbsOnlyFromRepresentationEqualityIsTrue :
      deriveKAbsOnlyFromRepresentationEquality ≡ true
    rationalEquivalenceAloneSufficesForKAbs : Bool
    rationalEquivalenceAloneSufficesForKAbsIsFalse :
      rationalEquivalenceAloneSufficesForKAbs ≡ false
    commonIndexTransportFallbackRequiredIfKAbsFails : Bool
    commonIndexTransportFallbackRequiredIfKAbsFailsIsTrue :
      commonIndexTransportFallbackRequiredIfKAbsFails ≡ true
    generalRebuildDivisionLemmaRequiredBeforeRetest : Bool
    generalRebuildDivisionLemmaRequiredBeforeRetestIsFalse :
      generalRebuildDivisionLemmaRequiredBeforeRetest ≡ false

canonicalKAbsMigrationDecision : KAbsMigrationDecision
canonicalKAbsMigrationDecision =
  kAbsMigrationDecision
    true refl
    false refl
    true refl
    true refl
    false refl
    true refl
    false refl

record PiYIntervalInterface (ExactReal : Set) : Set₁ where
  field
    embedRational : ℚ → ExactReal
    lessOrEqual : ExactReal → ExactReal → Set
    piExact : ExactReal
    observerMap : ExactReal → ExactReal

    piLower : ℚ
    piUpper : ℚ
    piContained :
      lessOrEqual (embedRational piLower) piExact
    piContainedUpper :
      lessOrEqual piExact (embedRational piUpper)

    yLower : ℚ
    yUpper : ℚ
    observerContained :
      lessOrEqual
        (embedRational yLower)
        (observerMap piExact)
    observerContainedUpper :
      lessOrEqual
        (observerMap piExact)
        (embedRational yUpper)

    observerMapDefinitionAtCanonicalApproximation :
      observerMap (embedRational Pi50.canonicalPi50)
      ≡ embedRational Pi50.canonicalY50

open PiYIntervalInterface public

record ExactRealArchitectureStatus : Set where
  constructor exactRealArchitectureStatus
  field
    finiteExceptionalLayerDependsOnBishop : Bool
    finiteExceptionalLayerDependsOnBishopIsFalse :
      finiteExceptionalLayerDependsOnBishop ≡ false
    bishopRetainedForTheoremPreservation : Bool
    bishopRetainedForTheoremPreservationIsTrue :
      bishopRetainedForTheoremPreservation ≡ true
    narrowPiYInterfaceExposed : Bool
    narrowPiYInterfaceExposedIsTrue :
      narrowPiYInterfaceExposed ≡ true
    cubicalPrototypeEscalated : Bool
    cubicalPrototypeEscalatedIsTrue :
      cubicalPrototypeEscalated ≡ true
    cubicalBackendSelectedUniversally : Bool
    cubicalBackendSelectedUniversallyIsFalse :
      cubicalBackendSelectedUniversally ≡ false
    constructivePiIntervalInstantiated : Bool
    constructivePiIntervalInstantiatedIsFalse :
      constructivePiIntervalInstantiated ≡ false

canonicalExactRealArchitectureStatus : ExactRealArchitectureStatus
canonicalExactRealArchitectureStatus =
  exactRealArchitectureStatus
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl

exactRealBackendBoundaryReceipt : GenericReceipt.GenericReceipt
exactRealBackendBoundaryReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bounded exact-real backend architecture"
    "DASHI.Foundations.UBP.ExactRealBackendBoundary"
    "canonicalExactRealArchitectureStatus"
    "Bishop theorem preservation, a narrow pi/Y rational-enclosure interface and a Cubical HoTT-real prototype are separated; the K-abs migration decision is compiler-led and has common-index transport as a fail-closed fallback"
    "no general real backend is declared universally suitable, and the constructive pi interval remains an explicit instantiation obligation"
    "agda -i . DASHI/Foundations/UBP/ExactRealBackendBoundary.agda"

exactRealBackendBoundaryReceiptNonPromoting :
  GenericReceipt.promotesClaim exactRealBackendBoundaryReceipt ≡ false
exactRealBackendBoundaryReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse exactRealBackendBoundaryReceipt
