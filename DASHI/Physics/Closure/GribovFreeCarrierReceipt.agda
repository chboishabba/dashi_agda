module DASHI.Physics.Closure.GribovFreeCarrierReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Core.Q using (ℚ)
open import Ontology.GodelLattice using (FactorVec)
import Ontology.Hecke.FactorVecInstances as FVI
import Ontology.Hecke.QuotientRepresentation as HQ
import DASHI.Physics.Closure.FactorVecDiscreteMetricTensorSurface as Metric

------------------------------------------------------------------------
-- Carrier-only Gribov-free receipt.
--
-- This is a canonical-representative / gauge-analogy receipt over the local
-- FactorVec identity quotient.  It records that the carrier layer has a
-- selected representative for each carrier class.  It is not a continuum
-- Yang-Mills Gribov theorem, does not prove global gauge fixing for
-- connections, and does not promote any Clay Yang-Mills claim.

data GribovFreeCarrierStatus : Set where
  factorVecIdentityQuotientHasCanonicalRepresentativeOnly :
    GribovFreeCarrierStatus

data GribovFreeCarrierCoordinateStatus : Set where
  identityQuotientFiberUnique :
    GribovFreeCarrierCoordinateStatus

  factorVecCoordinateProjectionPrimitiveRecorded :
    GribovFreeCarrierCoordinateStatus

  p2LorentzSignedCoordinateLawRecorded :
    GribovFreeCarrierCoordinateStatus

canonicalGribovFreeCarrierCoordinateStatus :
  List GribovFreeCarrierCoordinateStatus
canonicalGribovFreeCarrierCoordinateStatus =
  identityQuotientFiberUnique
  ∷ factorVecCoordinateProjectionPrimitiveRecorded
  ∷ p2LorentzSignedCoordinateLawRecorded
  ∷ []

data GribovFreeCarrierPromotion : Set where

gribovFreeCarrierPromotionImpossibleHere :
  GribovFreeCarrierPromotion →
  ⊥
gribovFreeCarrierPromotionImpossibleHere ()

carrierRepresentativeStatement : String
carrierRepresentativeStatement =
  "The local FactorVec identity quotient supplies a canonical representative for each carrier class; this is only a carrier gauge-analogy receipt."

notContinuumYMStatement : String
notContinuumYMStatement =
  "This receipt is not a continuum Yang-Mills Gribov theorem and does not assert global gauge fixing for smooth gauge connections."

noClayPromotionStatement : String
noClayPromotionStatement =
  "No Clay Yang-Mills, mass-gap, terminal, or millennium-problem promotion is introduced."

canonicalCarrierRepresentative :
  FactorVec →
  FactorVec
canonicalCarrierRepresentative =
  HQ.QuotientInterfaceOn.representative FVI.factorVecQuotient

canonicalCarrierRepresentativeSection :
  (v : FactorVec) →
  HQ.QuotientInterfaceOn.proj FVI.factorVecQuotient
    (canonicalCarrierRepresentative v)
  ≡ v
canonicalCarrierRepresentativeSection =
  HQ.QuotientInterfaceOn.section FVI.factorVecQuotient

carrierClassHasUniqueCanonicalRepresentative :
  (c s : FactorVec) →
  HQ.QuotientInterfaceOn.proj FVI.factorVecQuotient s ≡ c →
  s ≡ canonicalCarrierRepresentative c
carrierClassHasUniqueCanonicalRepresentative c s fiberEq =
  fiberEq

carrierCoordinateProjectionPrimitive :
  Metric.FactorVecTangentDirection →
  Metric.FactorVecQCoefficientVector →
  ℚ
carrierCoordinateProjectionPrimitive =
  Metric.factorVecQCoordinate

record GribovFreeCarrierReceipt : Set₁ where
  field
    status :
      GribovFreeCarrierStatus

    statusIsCanonical :
      status ≡ factorVecIdentityQuotientHasCanonicalRepresentativeOnly

    carrierQuotient :
      HQ.QuotientInterfaceOn FactorVec FactorVec

    carrierQuotientIsLocalFactorVecIdentity :
      carrierQuotient ≡ FVI.factorVecQuotient

    representative :
      FactorVec →
      FactorVec

    representativeIsCanonical :
      representative ≡ canonicalCarrierRepresentative

    representativeSection :
      (v : FactorVec) →
      HQ.QuotientInterfaceOn.proj FVI.factorVecQuotient (representative v)
      ≡ v

    uniqueRepresentativeInIdentityFiber :
      (c s : FactorVec) →
      HQ.QuotientInterfaceOn.proj FVI.factorVecQuotient s ≡ c →
      s ≡ canonicalCarrierRepresentative c

    uniqueRepresentativeIsCanonical :
      uniqueRepresentativeInIdentityFiber
      ≡
      carrierClassHasUniqueCanonicalRepresentative

    coordinateProjection :
      Metric.FactorVecTangentDirection →
      Metric.FactorVecQCoefficientVector →
      ℚ

    coordinateProjectionIsFactorVecQCoordinate :
      coordinateProjection ≡ carrierCoordinateProjectionPrimitive

    coordinateStatuses :
      List GribovFreeCarrierCoordinateStatus

    coordinateStatusesAreCanonical :
      coordinateStatuses ≡ canonicalGribovFreeCarrierCoordinateStatus

    localCanonicalRepresentativeRecorded :
      Bool

    localCanonicalRepresentativeRecordedIsTrue :
      localCanonicalRepresentativeRecorded ≡ true

    localUniqueFactorizationSurfaceOnly :
      Bool

    localUniqueFactorizationSurfaceOnlyIsTrue :
      localUniqueFactorizationSurfaceOnly ≡ true

    coordinateLawPrimitiveRecorded :
      Bool

    coordinateLawPrimitiveRecordedIsTrue :
      coordinateLawPrimitiveRecorded ≡ true

    p2LorentzSignedCoordinateLawWitnessRecorded :
      Bool

    p2LorentzSignedCoordinateLawWitnessRecordedIsTrue :
      p2LorentzSignedCoordinateLawWitnessRecorded ≡ true

    uniqueCoordinateRepresentativeRecorded :
      Bool

    uniqueCoordinateRepresentativeRecordedIsTrue :
      uniqueCoordinateRepresentativeRecorded ≡ true

    continuumYangMillsGribovTheorem :
      Bool

    continuumYangMillsGribovTheoremIsFalse :
      continuumYangMillsGribovTheorem ≡ false

    globalSmoothGaugeFixingClaim :
      Bool

    globalSmoothGaugeFixingClaimIsFalse :
      globalSmoothGaugeFixingClaim ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    promotionFlags :
      List GribovFreeCarrierPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    carrierRepresentativeReading :
      String

    carrierRepresentativeReadingIsCanonical :
      carrierRepresentativeReading ≡ carrierRepresentativeStatement

    notContinuumYMReading :
      String

    notContinuumYMReadingIsCanonical :
      notContinuumYMReading ≡ notContinuumYMStatement

    noClayPromotionReading :
      String

    noClayPromotionReadingIsCanonical :
      noClayPromotionReading ≡ noClayPromotionStatement

    receiptBoundary :
      List String

open GribovFreeCarrierReceipt public

canonicalGribovFreeCarrierReceipt :
  GribovFreeCarrierReceipt
canonicalGribovFreeCarrierReceipt =
  record
    { status =
        factorVecIdentityQuotientHasCanonicalRepresentativeOnly
    ; statusIsCanonical =
        refl
    ; carrierQuotient =
        FVI.factorVecQuotient
    ; carrierQuotientIsLocalFactorVecIdentity =
        refl
    ; representative =
        canonicalCarrierRepresentative
    ; representativeIsCanonical =
        refl
    ; representativeSection =
        canonicalCarrierRepresentativeSection
    ; uniqueRepresentativeInIdentityFiber =
        carrierClassHasUniqueCanonicalRepresentative
    ; uniqueRepresentativeIsCanonical =
        refl
    ; coordinateProjection =
        carrierCoordinateProjectionPrimitive
    ; coordinateProjectionIsFactorVecQCoordinate =
        refl
    ; coordinateStatuses =
        canonicalGribovFreeCarrierCoordinateStatus
    ; coordinateStatusesAreCanonical =
        refl
    ; localCanonicalRepresentativeRecorded =
        true
    ; localCanonicalRepresentativeRecordedIsTrue =
        refl
    ; localUniqueFactorizationSurfaceOnly =
        true
    ; localUniqueFactorizationSurfaceOnlyIsTrue =
        refl
    ; coordinateLawPrimitiveRecorded =
        true
    ; coordinateLawPrimitiveRecordedIsTrue =
        refl
    ; p2LorentzSignedCoordinateLawWitnessRecorded =
        true
    ; p2LorentzSignedCoordinateLawWitnessRecordedIsTrue =
        refl
    ; uniqueCoordinateRepresentativeRecorded =
        true
    ; uniqueCoordinateRepresentativeRecordedIsTrue =
        refl
    ; continuumYangMillsGribovTheorem =
        false
    ; continuumYangMillsGribovTheoremIsFalse =
        refl
    ; globalSmoothGaugeFixingClaim =
        false
    ; globalSmoothGaugeFixingClaimIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; carrierRepresentativeReading =
        carrierRepresentativeStatement
    ; carrierRepresentativeReadingIsCanonical =
        refl
    ; notContinuumYMReading =
        notContinuumYMStatement
    ; notContinuumYMReadingIsCanonical =
        refl
    ; noClayPromotionReading =
        noClayPromotionStatement
    ; noClayPromotionReadingIsCanonical =
        refl
    ; receiptBoundary =
        "The consumed surface is Ontology.Hecke.FactorVecInstances.factorVecQuotient"
        ∷ "The representative is the identity representative for the local FactorVec carrier class"
        ∷ "The identity quotient fiber has a unique canonical representative by the concrete proj=id section"
        ∷ "The coordinate primitive is FactorVecDiscreteMetricTensorSurface.factorVecQCoordinate with the existing p2-Lorentz signed coordinate-law witness"
        ∷ "The Gribov-free wording is only a canonical-representative/gauge-analogy reading"
        ∷ "No continuum Yang-Mills Gribov theorem or smooth global gauge-fixing theorem is proved"
        ∷ "No Clay Yang-Mills, mass-gap, terminal, or millennium-problem promotion is made"
        ∷ []
    }

canonicalGribovFreeCarrierHasRepresentative :
  localCanonicalRepresentativeRecorded canonicalGribovFreeCarrierReceipt ≡ true
canonicalGribovFreeCarrierHasRepresentative =
  refl

canonicalGribovFreeCarrierHasUniqueRepresentative :
  uniqueCoordinateRepresentativeRecorded canonicalGribovFreeCarrierReceipt
  ≡ true
canonicalGribovFreeCarrierHasUniqueRepresentative =
  refl

canonicalGribovFreeCarrierHasCoordinatePrimitive :
  coordinateLawPrimitiveRecorded canonicalGribovFreeCarrierReceipt ≡ true
canonicalGribovFreeCarrierHasCoordinatePrimitive =
  refl

canonicalGribovFreeCarrierNotContinuumYM :
  continuumYangMillsGribovTheorem canonicalGribovFreeCarrierReceipt ≡ false
canonicalGribovFreeCarrierNotContinuumYM =
  refl

canonicalGribovFreeCarrierNoGlobalGaugeFixing :
  globalSmoothGaugeFixingClaim canonicalGribovFreeCarrierReceipt ≡ false
canonicalGribovFreeCarrierNoGlobalGaugeFixing =
  refl

canonicalGribovFreeCarrierNoClayPromotion :
  clayYangMillsPromoted canonicalGribovFreeCarrierReceipt ≡ false
canonicalGribovFreeCarrierNoClayPromotion =
  refl

canonicalGribovFreeCarrierNoPromotion :
  GribovFreeCarrierPromotion →
  ⊥
canonicalGribovFreeCarrierNoPromotion =
  gribovFreeCarrierPromotionImpossibleHere
