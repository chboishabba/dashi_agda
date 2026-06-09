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
-- selected representative for each carrier class.  The "Gribov-free" reading
-- is discrete/carrier-only: continuum Gribov copies persist unless separately
-- handled, Singer's obstruction to a global smooth gauge section is not
-- defeated, Gate3/continuum lift remains open, and no Clay Yang-Mills claim is
-- promoted.
-- The braid/KP correction is also explicit: the carrier representative does
-- not imply a Yang-Baxter theorem or a KP theorem.

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
  "This receipt is not a continuum Yang-Mills Gribov theorem: continuum Gribov copies persist unless a separate continuum gauge-slice argument handles them."

singerTheoremBoundaryStatement : String
singerTheoremBoundaryStatement =
  "Singer's obstruction to a global smooth gauge section is not defeated by the carrier canonical representative."

gate3ContinuumLiftOpenStatement : String
gate3ContinuumLiftOpenStatement =
  "Gate3/continuum lift remains open; the carrier representative does not close the continuum Yang-Mills lift."

noClayPromotionStatement : String
noClayPromotionStatement =
  "No Clay Yang-Mills, mass-gap, terminal, millennium-problem, Yang-Baxter, or KP theorem promotion is introduced."

braidKPBoundaryStatement : String
braidKPBoundaryStatement =
  "The carrier representative is not a Yang-Baxter theorem or KP theorem."

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

    continuumGribovCopiesResolved :
      Bool

    continuumGribovCopiesResolvedIsFalse :
      continuumGribovCopiesResolved ≡ false

    singerGlobalSectionObstructionDefeated :
      Bool

    singerGlobalSectionObstructionDefeatedIsFalse :
      singerGlobalSectionObstructionDefeated ≡ false

    gate3ContinuumLiftClosed :
      Bool

    gate3ContinuumLiftClosedIsFalse :
      gate3ContinuumLiftClosed ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    yangBaxterTheoremPromoted :
      Bool

    yangBaxterTheoremPromotedIsFalse :
      yangBaxterTheoremPromoted ≡ false

    kpTheoremPromoted :
      Bool

    kpTheoremPromotedIsFalse :
      kpTheoremPromoted ≡ false

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

    singerTheoremBoundaryReading :
      String

    singerTheoremBoundaryReadingIsCanonical :
      singerTheoremBoundaryReading ≡ singerTheoremBoundaryStatement

    gate3ContinuumLiftOpenReading :
      String

    gate3ContinuumLiftOpenReadingIsCanonical :
      gate3ContinuumLiftOpenReading ≡ gate3ContinuumLiftOpenStatement

    noClayPromotionReading :
      String

    noClayPromotionReadingIsCanonical :
      noClayPromotionReading ≡ noClayPromotionStatement

    braidKPBoundaryReading :
      String

    braidKPBoundaryReadingIsCanonical :
      braidKPBoundaryReading ≡ braidKPBoundaryStatement

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
    ; continuumGribovCopiesResolved =
        false
    ; continuumGribovCopiesResolvedIsFalse =
        refl
    ; singerGlobalSectionObstructionDefeated =
        false
    ; singerGlobalSectionObstructionDefeatedIsFalse =
        refl
    ; gate3ContinuumLiftClosed =
        false
    ; gate3ContinuumLiftClosedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; yangBaxterTheoremPromoted =
        false
    ; yangBaxterTheoremPromotedIsFalse =
        refl
    ; kpTheoremPromoted =
        false
    ; kpTheoremPromotedIsFalse =
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
    ; singerTheoremBoundaryReading =
        singerTheoremBoundaryStatement
    ; singerTheoremBoundaryReadingIsCanonical =
        refl
    ; gate3ContinuumLiftOpenReading =
        gate3ContinuumLiftOpenStatement
    ; gate3ContinuumLiftOpenReadingIsCanonical =
        refl
    ; noClayPromotionReading =
        noClayPromotionStatement
    ; noClayPromotionReadingIsCanonical =
        refl
    ; braidKPBoundaryReading =
        braidKPBoundaryStatement
    ; braidKPBoundaryReadingIsCanonical =
        refl
    ; receiptBoundary =
        "The consumed surface is Ontology.Hecke.FactorVecInstances.factorVecQuotient"
        ∷ "The representative is the identity representative for the local FactorVec carrier class"
        ∷ "The identity quotient fiber has a unique canonical representative by the concrete proj=id section"
        ∷ "The coordinate primitive is FactorVecDiscreteMetricTensorSurface.factorVecQCoordinate with the existing p2-Lorentz signed coordinate-law witness"
        ∷ "The Gribov-free wording is only a discrete carrier canonical-representative/gauge-analogy reading"
        ∷ "Continuum Gribov copies persist unless separately handled by a continuum gauge-slice argument"
        ∷ "No continuum Yang-Mills Gribov theorem or smooth global gauge-fixing theorem is proved"
        ∷ "Singer's obstruction to a global smooth gauge section is not defeated here"
        ∷ "Gate3/continuum lift remains open"
        ∷ "No Yang-Baxter theorem or KP theorem is promoted"
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

canonicalGribovFreeCarrierContinuumCopiesUnresolved :
  continuumGribovCopiesResolved canonicalGribovFreeCarrierReceipt ≡ false
canonicalGribovFreeCarrierContinuumCopiesUnresolved =
  refl

canonicalGribovFreeCarrierSingerNotDefeated :
  singerGlobalSectionObstructionDefeated canonicalGribovFreeCarrierReceipt
  ≡ false
canonicalGribovFreeCarrierSingerNotDefeated =
  refl

canonicalGribovFreeCarrierGate3ContinuumLiftOpen :
  gate3ContinuumLiftClosed canonicalGribovFreeCarrierReceipt ≡ false
canonicalGribovFreeCarrierGate3ContinuumLiftOpen =
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

canonicalGribovFreeCarrierNoYangBaxterPromotion :
  yangBaxterTheoremPromoted canonicalGribovFreeCarrierReceipt ≡ false
canonicalGribovFreeCarrierNoYangBaxterPromotion =
  refl

canonicalGribovFreeCarrierNoKPPromotion :
  kpTheoremPromoted canonicalGribovFreeCarrierReceipt ≡ false
canonicalGribovFreeCarrierNoKPPromotion =
  refl
