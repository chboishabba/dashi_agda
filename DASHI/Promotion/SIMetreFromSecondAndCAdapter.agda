module DASHI.Promotion.SIMetreFromSecondAndCAdapter where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Constants.Registry as Registry
import DASHI.Physics.Closure.AtomicClockSISecondCalibrationBridge as Atomic
import DASHI.Promotion.NumericAuthorityPayloadValidator as Payload
import DASHI.Promotion.RydbergClockMetreBridge as Rydberg
import DASHI.Promotion.SIDefiningConstantsAuthorityArtifactRequest as SIRequest

------------------------------------------------------------------------
-- SI metre adapter from the exact SI second and exact speed of light.
--
-- This module is the promotion-lane adapter for the derived metre carrier.
-- It deliberately constructs only the exact SI dimensional/narrative route:
--  * the second side is inherited from the atomic-clock SI bridge;
--  * the speed-of-light integer is the exact SI defining value 299792458;
--  * the metre narrative is "metre = c * second / 299792458";
--  * the Rydberg/wavenumber route is exposed only as a dimension carrier.
--
-- It does not accept a BIPM artifact payload, a spectroscopy token, a
-- CODATA R_infinity value, a NIST ASD line, or any chemistry/spectroscopy
-- promotion.  Those guards are fields of the canonical adapter.

data SIMetreCarrierUnit : Set where
  siSecondUnit :
    SIMetreCarrierUnit

  speedOfLightUnit :
    SIMetreCarrierUnit

  siMetreUnit :
    SIMetreCarrierUnit

  wavenumberUnit :
    SIMetreCarrierUnit

record SIMetreDimensionRoute : Set₁ where
  field
    routeLabel :
      String

    carrierUnit :
      SIMetreCarrierUnit

    symbolText :
      String

    canonicalUnitText :
      String

    dimensionRoute :
      Rydberg.DimensionVectorRoute

    sourceRef :
      String

    promotedByThisAdapter :
      Bool

    promotedByThisAdapterIsFalse :
      promotedByThisAdapter ≡ false

open SIMetreDimensionRoute public

mkAdapterRoute :
  String →
  SIMetreCarrierUnit →
  String →
  String →
  Rydberg.DimensionVectorRoute →
  String →
  SIMetreDimensionRoute
mkAdapterRoute label unit symbol canonical route ref =
  record
    { routeLabel =
        label
    ; carrierUnit =
        unit
    ; symbolText =
        symbol
    ; canonicalUnitText =
        canonical
    ; dimensionRoute =
        route
    ; sourceRef =
        ref
    ; promotedByThisAdapter =
        false
    ; promotedByThisAdapterIsFalse =
        refl
    }

secondUnitDimensionRoute : SIMetreDimensionRoute
secondUnitDimensionRoute =
  mkAdapterRoute
    "SI second inherited from atomic-clock calibration bridge"
    siSecondUnit
    "s"
    "second"
    Rydberg.secondDimensionRoute
    "DASHI.Physics.Closure.AtomicClockSISecondCalibrationBridge.canonicalCs133SISecondAnchor"

speedOfLightUnitDimensionRoute : SIMetreDimensionRoute
speedOfLightUnitDimensionRoute =
  mkAdapterRoute
    "exact speed of light dependency in m s^-1"
    speedOfLightUnit
    "c"
    "m s^-1"
    Rydberg.metreDimensionRoute
    "DASHI.Promotion.SIDefiningConstantsAuthorityArtifactRequest.canonicalCRegistryRow"

metreUnitDimensionRoute : SIMetreDimensionRoute
metreUnitDimensionRoute =
  mkAdapterRoute
    "SI metre derived-unit carrier from second and exact c"
    siMetreUnit
    "m"
    "metre"
    Rydberg.metreDimensionRoute
    "DASHI.Promotion.RydbergClockMetreBridge.metreDimensionRoute"

wavenumberUnitDimensionRoute : SIMetreDimensionRoute
wavenumberUnitDimensionRoute =
  mkAdapterRoute
    "Rydberg wavenumber dimension carrier"
    wavenumberUnit
    "R_infinity"
    "m^-1"
    Rydberg.wavenumberDimensionRoute
    "DASHI.Promotion.RydbergClockMetreBridge.wavenumberDimensionRoute"

canonicalSIMetreDimensionRoutes : List SIMetreDimensionRoute
canonicalSIMetreDimensionRoutes =
  secondUnitDimensionRoute
  ∷ speedOfLightUnitDimensionRoute
  ∷ metreUnitDimensionRoute
  ∷ wavenumberUnitDimensionRoute
  ∷ []

speedOfLightExactInteger : Nat
speedOfLightExactInteger =
  299792458

record ExactSpeedOfLightDependency : Set₁ where
  field
    dependencyLabel :
      String

    registryRow :
      Registry.KnownConstantSlot

    authorityArtifactRequest :
      SIRequest.SIDefiningConstantAuthorityArtifactRowRequest

    exactInteger :
      Nat

    exactIntegerIsCanonicalC :
      exactInteger ≡ speedOfLightExactInteger

    registryValueText :
      String

    registryUnitText :
      String

    registryValueTextIsCanonical :
      registryValueText ≡ "299792458"

    registryUnitTextIsCanonical :
      registryUnitText ≡ "m s^-1"

    exactBySIDefinition :
      Bool

    exactBySIDefinitionIsTrue :
      exactBySIDefinition ≡ true

    artifactPayloadAccepted :
      Bool

    artifactPayloadAcceptedIsFalse :
      artifactPayloadAccepted ≡ false

open ExactSpeedOfLightDependency public

canonicalExactSpeedOfLightDependency : ExactSpeedOfLightDependency
canonicalExactSpeedOfLightDependency =
  record
    { dependencyLabel =
        "speed of light in vacuum exact SI defining dependency"
    ; registryRow =
        SIRequest.canonicalCRegistryRow
    ; authorityArtifactRequest =
        SIRequest.canonicalCAuthorityArtifactRowRequest
    ; exactInteger =
        speedOfLightExactInteger
    ; exactIntegerIsCanonicalC =
        refl
    ; registryValueText =
        Registry.KnownConstantSlot.value SIRequest.canonicalCRegistryRow
    ; registryUnitText =
        Registry.KnownConstantSlot.unit SIRequest.canonicalCRegistryRow
    ; registryValueTextIsCanonical =
        SIRequest.canonicalCRowValueIsCanonical
    ; registryUnitTextIsCanonical =
        SIRequest.canonicalCRowUnitIsCanonical
    ; exactBySIDefinition =
        true
    ; exactBySIDefinitionIsTrue =
        refl
    ; artifactPayloadAccepted =
        SIRequest.SIDefiningConstantAuthorityArtifactRowRequest.artifactAccepted
          SIRequest.canonicalCAuthorityArtifactRowRequest
    ; artifactPayloadAcceptedIsFalse =
        SIRequest.SIDefiningConstantAuthorityArtifactRowRequest.artifactAcceptedIsFalse
          SIRequest.canonicalCAuthorityArtifactRowRequest
    }

record MetreFromSecondAndCNarrative : Set₁ where
  field
    narrativeLabel :
      String

    secondAnchor :
      Atomic.Cs133SISecondAnchor

    cDependency :
      ExactSpeedOfLightDependency

    numeratorConstant :
      String

    denominatorExactInteger :
      Nat

    denominatorIsExactC :
      denominatorExactInteger ≡ speedOfLightExactInteger

    equationText :
      String

    derivedUnitText :
      String

    consumesSecondRoute :
      SIMetreDimensionRoute

    consumesCUnitRoute :
      SIMetreDimensionRoute

    yieldsMetreRoute :
      SIMetreDimensionRoute

    metreLengthExponentIsPlusOne :
      Rydberg.lengthExponent
        (SIMetreDimensionRoute.dimensionRoute yieldsMetreRoute)
      ≡
      Rydberg.plusOne

    metreTimeExponentIsZero :
      Rydberg.timeExponent
        (SIMetreDimensionRoute.dimensionRoute yieldsMetreRoute)
      ≡
      Rydberg.zero

open MetreFromSecondAndCNarrative public

canonicalMetreFromSecondAndCNarrative :
  MetreFromSecondAndCNarrative
canonicalMetreFromSecondAndCNarrative =
  record
    { narrativeLabel =
        "metre = c * second / 299792458 exact SI derivation route"
    ; secondAnchor =
        Atomic.canonicalCs133SISecondAnchor
    ; cDependency =
        canonicalExactSpeedOfLightDependency
    ; numeratorConstant =
        "c * second"
    ; denominatorExactInteger =
        speedOfLightExactInteger
    ; denominatorIsExactC =
        refl
    ; equationText =
        "metre = c * second / 299792458"
    ; derivedUnitText =
        "m"
    ; consumesSecondRoute =
        secondUnitDimensionRoute
    ; consumesCUnitRoute =
        speedOfLightUnitDimensionRoute
    ; yieldsMetreRoute =
        metreUnitDimensionRoute
    ; metreLengthExponentIsPlusOne =
        refl
    ; metreTimeExponentIsZero =
        refl
    }

record RydbergWavenumberDimensionAdapter : Set₁ where
  field
    adapterLabel :
      String

    rydbergBridge :
      Rydberg.RydbergClockMetreBridge

    wavenumberRoute :
      SIMetreDimensionRoute

    routeExpression :
      String

    lengthExponentIsMinusOne :
      Rydberg.lengthExponent
        (SIMetreDimensionRoute.dimensionRoute wavenumberRoute)
      ≡
      Rydberg.minusOne

    timeExponentIsZero :
      Rydberg.timeExponent
        (SIMetreDimensionRoute.dimensionRoute wavenumberRoute)
      ≡
      Rydberg.zero

    codataRInfinityPayloadRequired :
      Bool

    codataRInfinityPayloadRequiredIsTrue :
      codataRInfinityPayloadRequired ≡ true

    spectroscopyPromotion :
      Bool

    spectroscopyPromotionIsFalse :
      spectroscopyPromotion ≡ false

open RydbergWavenumberDimensionAdapter public

canonicalRydbergWavenumberDimensionAdapter :
  RydbergWavenumberDimensionAdapter
canonicalRydbergWavenumberDimensionAdapter =
  record
    { adapterLabel =
        "Rydberg wavenumber dimension only; no spectroscopy promotion"
    ; rydbergBridge =
        Rydberg.canonicalRydbergClockMetreBridge
    ; wavenumberRoute =
        wavenumberUnitDimensionRoute
    ; routeExpression =
        "wavenumber = 1 / lambda; R_infinity is carried as m^-1"
    ; lengthExponentIsMinusOne =
        refl
    ; timeExponentIsZero =
        refl
    ; codataRInfinityPayloadRequired =
        Rydberg.rInfinityCODATAMeasuredPayloadStillRequired
          Rydberg.canonicalRydbergClockMetreBridge
    ; codataRInfinityPayloadRequiredIsTrue =
        Rydberg.canonicalBridgeRydbergMeasuredPayloadStillRequired
    ; spectroscopyPromotion =
        Rydberg.spectroscopyPromotion
          Rydberg.canonicalRydbergClockMetreBridge
    ; spectroscopyPromotionIsFalse =
        Rydberg.canonicalBridgeSpectroscopyPromotionIsFalse
    }

record SIMetreFailClosedGuards : Set₁ where
  field
    guardLabel :
      String

    siAuthorityManifest :
      SIRequest.SIDefiningConstantsAuthorityArtifactRequestManifest

    cAuthorityRequest :
      SIRequest.SIDefiningConstantAuthorityArtifactRowRequest

    payloadValidator :
      Payload.NumericAuthorityPayloadValidatorReceipt

    cArtifactLoaded :
      Bool

    cArtifactLoadedIsFalse :
      cArtifactLoaded ≡ false

    cArtifactAccepted :
      Bool

    cArtifactAcceptedIsFalse :
      cArtifactAccepted ≡ false

    cRowPromoted :
      Bool

    cRowPromotedIsFalse :
      cRowPromoted ≡ false

    manifestAnyRowPromoted :
      Bool

    manifestAnyRowPromotedIsFalse :
      manifestAnyRowPromoted ≡ false

    spectroscopyPromotion :
      Bool

    spectroscopyPromotionIsFalse :
      spectroscopyPromotion ≡ false

    acceptedSpectroscopyAuthorityTokenPresent :
      Bool

    acceptedSpectroscopyAuthorityTokenPresentIsFalse :
      acceptedSpectroscopyAuthorityTokenPresent ≡ false

    metreCarrierDerived :
      Bool

    metreCarrierDerivedIsTrue :
      metreCarrierDerived ≡ true

open SIMetreFailClosedGuards public

canonicalSIMetreFailClosedGuards : SIMetreFailClosedGuards
canonicalSIMetreFailClosedGuards =
  record
    { guardLabel =
        "SI metre carrier derived while authority payload and spectroscopy promotion remain closed"
    ; siAuthorityManifest =
        SIRequest.canonicalSIDefiningConstantsAuthorityArtifactRequestManifest
    ; cAuthorityRequest =
        SIRequest.canonicalCAuthorityArtifactRowRequest
    ; payloadValidator =
        Payload.canonicalNumericAuthorityPayloadValidatorReceipt
    ; cArtifactLoaded =
        SIRequest.SIDefiningConstantAuthorityArtifactRowRequest.artifactLoaded
          SIRequest.canonicalCAuthorityArtifactRowRequest
    ; cArtifactLoadedIsFalse =
        SIRequest.SIDefiningConstantAuthorityArtifactRowRequest.artifactLoadedIsFalse
          SIRequest.canonicalCAuthorityArtifactRowRequest
    ; cArtifactAccepted =
        SIRequest.SIDefiningConstantAuthorityArtifactRowRequest.artifactAccepted
          SIRequest.canonicalCAuthorityArtifactRowRequest
    ; cArtifactAcceptedIsFalse =
        SIRequest.SIDefiningConstantAuthorityArtifactRowRequest.artifactAcceptedIsFalse
          SIRequest.canonicalCAuthorityArtifactRowRequest
    ; cRowPromoted =
        SIRequest.SIDefiningConstantAuthorityArtifactRowRequest.rowPromoted
          SIRequest.canonicalCAuthorityArtifactRowRequest
    ; cRowPromotedIsFalse =
        SIRequest.SIDefiningConstantAuthorityArtifactRowRequest.rowPromotedIsFalse
          SIRequest.canonicalCAuthorityArtifactRowRequest
    ; manifestAnyRowPromoted =
        SIRequest.SIDefiningConstantsAuthorityArtifactRequestManifest.anyRowPromoted
          SIRequest.canonicalSIDefiningConstantsAuthorityArtifactRequestManifest
    ; manifestAnyRowPromotedIsFalse =
        SIRequest.SIDefiningConstantsAuthorityArtifactRequestManifest.anyRowPromotedIsFalse
          SIRequest.canonicalSIDefiningConstantsAuthorityArtifactRequestManifest
    ; spectroscopyPromotion =
        Rydberg.spectroscopyPromotion
          Rydberg.canonicalRydbergClockMetreBridge
    ; spectroscopyPromotionIsFalse =
        Rydberg.canonicalBridgeSpectroscopyPromotionIsFalse
    ; acceptedSpectroscopyAuthorityTokenPresent =
        Rydberg.acceptedAuthorityTokenPresent
          Rydberg.canonicalRydbergClockMetreBridge
    ; acceptedSpectroscopyAuthorityTokenPresentIsFalse =
        Rydberg.canonicalBridgeAuthorityTokenStillMissing
    ; metreCarrierDerived =
        true
    ; metreCarrierDerivedIsTrue =
        refl
    }

record SIMetreFromSecondAndCAdapter : Set₁ where
  field
    adapterLabel :
      String

    sourceRefs :
      List String

    atomicSecondAnchor :
      Atomic.Cs133SISecondAnchor

    speedOfLightDependency :
      ExactSpeedOfLightDependency

    metreNarrative :
      MetreFromSecondAndCNarrative

    metreRoute :
      SIMetreDimensionRoute

    wavenumberAdapter :
      RydbergWavenumberDimensionAdapter

    failClosedGuards :
      SIMetreFailClosedGuards

    routeInventory :
      List SIMetreDimensionRoute

    exactCIntegerDependency :
      Nat

    exactCIntegerDependencyIsCanonical :
      exactCIntegerDependency ≡ speedOfLightExactInteger

    cs133IntegerDependency :
      Nat

    cs133IntegerDependencyIsCanonical :
      cs133IntegerDependency ≡ Atomic.cs133ExactInteger

    metreEquation :
      String

    metreEquationIsCanonical :
      metreEquation ≡ "metre = c * second / 299792458"

    authorityPayloadPromoted :
      Bool

    authorityPayloadPromotedIsFalse :
      authorityPayloadPromoted ≡ false

    spectroscopyPromoted :
      Bool

    spectroscopyPromotedIsFalse :
      spectroscopyPromoted ≡ false

    derivedMetreCarrierAvailable :
      Bool

    derivedMetreCarrierAvailableIsTrue :
      derivedMetreCarrierAvailable ≡ true

open SIMetreFromSecondAndCAdapter public

canonicalSourceRefs : List String
canonicalSourceRefs =
  "DASHI.Physics.Closure.AtomicClockSISecondCalibrationBridge"
  ∷ "DASHI.Promotion.RydbergClockMetreBridge"
  ∷ "DASHI.Promotion.SIDefiningConstantsAuthorityArtifactRequest"
  ∷ "DASHI.Constants.Registry.canonicalSIDefiningConstants"
  ∷ []

canonicalSIMetreFromSecondAndCAdapter :
  SIMetreFromSecondAndCAdapter
canonicalSIMetreFromSecondAndCAdapter =
  record
    { adapterLabel =
        "substantive SI metre derivation adapter from second plus exact c"
    ; sourceRefs =
        canonicalSourceRefs
    ; atomicSecondAnchor =
        Atomic.canonicalCs133SISecondAnchor
    ; speedOfLightDependency =
        canonicalExactSpeedOfLightDependency
    ; metreNarrative =
        canonicalMetreFromSecondAndCNarrative
    ; metreRoute =
        metreUnitDimensionRoute
    ; wavenumberAdapter =
        canonicalRydbergWavenumberDimensionAdapter
    ; failClosedGuards =
        canonicalSIMetreFailClosedGuards
    ; routeInventory =
        canonicalSIMetreDimensionRoutes
    ; exactCIntegerDependency =
        speedOfLightExactInteger
    ; exactCIntegerDependencyIsCanonical =
        refl
    ; cs133IntegerDependency =
        Atomic.Cs133SISecondAnchor.exactInteger
          Atomic.canonicalCs133SISecondAnchor
    ; cs133IntegerDependencyIsCanonical =
        Atomic.canonicalAtomicClockCs133IntegerExact
    ; metreEquation =
        "metre = c * second / 299792458"
    ; metreEquationIsCanonical =
        refl
    ; authorityPayloadPromoted =
        SIMetreFailClosedGuards.manifestAnyRowPromoted
          canonicalSIMetreFailClosedGuards
    ; authorityPayloadPromotedIsFalse =
        SIMetreFailClosedGuards.manifestAnyRowPromotedIsFalse
          canonicalSIMetreFailClosedGuards
    ; spectroscopyPromoted =
        SIMetreFailClosedGuards.spectroscopyPromotion
          canonicalSIMetreFailClosedGuards
    ; spectroscopyPromotedIsFalse =
        SIMetreFailClosedGuards.spectroscopyPromotionIsFalse
          canonicalSIMetreFailClosedGuards
    ; derivedMetreCarrierAvailable =
        true
    ; derivedMetreCarrierAvailableIsTrue =
        refl
    }

canonicalAdapterMetreLengthExponentIsPlusOne :
  Rydberg.lengthExponent
    (SIMetreDimensionRoute.dimensionRoute
      (SIMetreFromSecondAndCAdapter.metreRoute
        canonicalSIMetreFromSecondAndCAdapter))
  ≡
  Rydberg.plusOne
canonicalAdapterMetreLengthExponentIsPlusOne =
  refl

canonicalAdapterMetreTimeExponentIsZero :
  Rydberg.timeExponent
    (SIMetreDimensionRoute.dimensionRoute
      (SIMetreFromSecondAndCAdapter.metreRoute
        canonicalSIMetreFromSecondAndCAdapter))
  ≡
  Rydberg.zero
canonicalAdapterMetreTimeExponentIsZero =
  refl

canonicalAdapterWavenumberLengthExponentIsMinusOne :
  Rydberg.lengthExponent
    (SIMetreDimensionRoute.dimensionRoute
      (RydbergWavenumberDimensionAdapter.wavenumberRoute
        (SIMetreFromSecondAndCAdapter.wavenumberAdapter
          canonicalSIMetreFromSecondAndCAdapter)))
  ≡
  Rydberg.minusOne
canonicalAdapterWavenumberLengthExponentIsMinusOne =
  refl

canonicalAdapterExactCIntegerDependency :
  SIMetreFromSecondAndCAdapter.exactCIntegerDependency
    canonicalSIMetreFromSecondAndCAdapter
  ≡
  299792458
canonicalAdapterExactCIntegerDependency =
  refl

canonicalAdapterAuthorityPayloadPromotedIsFalse :
  SIMetreFromSecondAndCAdapter.authorityPayloadPromoted
    canonicalSIMetreFromSecondAndCAdapter
  ≡
  false
canonicalAdapterAuthorityPayloadPromotedIsFalse =
  SIMetreFromSecondAndCAdapter.authorityPayloadPromotedIsFalse
    canonicalSIMetreFromSecondAndCAdapter

canonicalAdapterSpectroscopyPromotedIsFalse :
  SIMetreFromSecondAndCAdapter.spectroscopyPromoted
    canonicalSIMetreFromSecondAndCAdapter
  ≡
  false
canonicalAdapterSpectroscopyPromotedIsFalse =
  SIMetreFromSecondAndCAdapter.spectroscopyPromotedIsFalse
    canonicalSIMetreFromSecondAndCAdapter

canonicalAdapterDerivedMetreCarrierAvailable :
  SIMetreFromSecondAndCAdapter.derivedMetreCarrierAvailable
    canonicalSIMetreFromSecondAndCAdapter
  ≡
  true
canonicalAdapterDerivedMetreCarrierAvailable =
  refl
