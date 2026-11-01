module DASHI.Promotion.SIExactConstantConsumerIngestionBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.AtomicClockSISecondCalibrationBridge as Atomic
import DASHI.Physics.Closure.StoneSISecondTimeParameterBridge as Stone
import DASHI.Promotion.PlanckHbarSIPayloadRequest as Planck
import DASHI.Promotion.SIExactConstantParsedCarrierRequest as Parsed
import DASHI.Promotion.SIDefiningConstantsAuthorityArtifactRequest as Artifact
import DASHI.Promotion.SIMetreFromSecondAndCAdapter as Metre

------------------------------------------------------------------------
-- Consumer-ingestion bridge for exact parsed SI constants.
--
-- This surface is intentionally fail-closed.  It records the exact consumer
-- route that each parsed SI defining constant must feed next:
--   Delta nu Cs -> atomic-clock SI second route,
--   c           -> metre-from-second-and-c adapter,
--   h           -> hbar / Stone-Schrodinger lane.
--
-- The module does not accept a BIPM/NIST artifact, construct an authority
-- token, create a consumer ingestion receipt, or promote any numeric value.
-- It only ties existing parsed-carrier request rows to named downstream
-- consumers and keeps the terminal ingestion/promote guards false.

data ExactSIConsumerTarget : Set where
  cs133SISecondRouteTarget :
    ExactSIConsumerTarget

  speedOfLightMetreRouteTarget :
    ExactSIConsumerTarget

  planckHbarStoneRouteTarget :
    ExactSIConsumerTarget

data ConsumerIngestionPayloadTextKey : Set where
  consumerTargetKey :
    ConsumerIngestionPayloadTextKey

  parsedCarrierRowRefKey :
    ConsumerIngestionPayloadTextKey

  rawAuthorityTextKey :
    ConsumerIngestionPayloadTextKey

  parsedCarrierTextKey :
    ConsumerIngestionPayloadTextKey

  unitConventionTextKey :
    ConsumerIngestionPayloadTextKey

  dimensionalDependencyTextKey :
    ConsumerIngestionPayloadTextKey

  consumerRouteDependencyTextKey :
    ConsumerIngestionPayloadTextKey

  authorityWallTextKey :
    ConsumerIngestionPayloadTextKey

canonicalConsumerIngestionPayloadTextKeys :
  List ConsumerIngestionPayloadTextKey
canonicalConsumerIngestionPayloadTextKeys =
  consumerTargetKey
  ∷ parsedCarrierRowRefKey
  ∷ rawAuthorityTextKey
  ∷ parsedCarrierTextKey
  ∷ unitConventionTextKey
  ∷ dimensionalDependencyTextKey
  ∷ consumerRouteDependencyTextKey
  ∷ authorityWallTextKey
  ∷ []

record ConsumerIngestionPayloadText : Set where
  field
    constantSymbol :
      String

    consumerTarget :
      ExactSIConsumerTarget

    parsedCarrierRowRef :
      String

    rawAuthorityText :
      String

    parsedCarrierText :
      String

    unitConventionText :
      String

    dimensionalDependencyText :
      String

    consumerRouteDependencyText :
      String

    authorityWallText :
      String

open ConsumerIngestionPayloadText public

record ParsedCarrierDependency : Set₁ where
  field
    dependencyLabel :
      String

    parsedManifest :
      Parsed.SIExactConstantParsedCarrierRequestManifest

    parsedRow :
      Parsed.SIExactParsedCarrierRowRequest

    carrierKind :
      Parsed.SIExactParsedCarrierKind

    carrierKindMatchesRow :
      carrierKind ≡ Parsed.carrierKind parsedRow

    rawText :
      String

    rawTextMatchesParsedRow :
      rawText ≡ Parsed.rawAuthorityText parsedRow

    unitText :
      String

    unitTextMatchesParsedRow :
      unitText ≡ Parsed.unitText parsedRow

    parsedCarrierStructurallySupplied :
      Bool

    parsedCarrierStructurallySuppliedIsTrue :
      parsedCarrierStructurallySupplied ≡ true

    authorityArtifactPresent :
      Bool

    authorityArtifactPresentIsFalse :
      authorityArtifactPresent ≡ false

    consumerIngestionReceiptPresent :
      Bool

    consumerIngestionReceiptPresentIsFalse :
      consumerIngestionReceiptPresent ≡ false

open ParsedCarrierDependency public

mkParsedCarrierDependency :
  String →
  Parsed.SIExactParsedCarrierRowRequest →
  ParsedCarrierDependency
mkParsedCarrierDependency label row =
  record
    { dependencyLabel =
        label
    ; parsedManifest =
        Parsed.canonicalSIExactConstantParsedCarrierRequestManifest
    ; parsedRow =
        row
    ; carrierKind =
        Parsed.carrierKind row
    ; carrierKindMatchesRow =
        refl
    ; rawText =
        Parsed.rawAuthorityText row
    ; rawTextMatchesParsedRow =
        refl
    ; unitText =
        Parsed.unitText row
    ; unitTextMatchesParsedRow =
        refl
    ; parsedCarrierStructurallySupplied =
        Parsed.parsedCarrierStructurallySupplied row
    ; parsedCarrierStructurallySuppliedIsTrue =
        Parsed.parsedCarrierStructurallySuppliedIsTrue row
    ; authorityArtifactPresent =
        Parsed.authorityArtifactPresent row
    ; authorityArtifactPresentIsFalse =
        Parsed.authorityArtifactPresentIsFalse row
    ; consumerIngestionReceiptPresent =
        Parsed.consumerIngestionReceiptPresent row
    ; consumerIngestionReceiptPresentIsFalse =
        Parsed.consumerIngestionReceiptPresentIsFalse row
    }

record DimensionalDependency : Set where
  field
    dimensionLabel :
      String

    unitText :
      String

    sourceDimensionRef :
      String

    consumerDimensionRef :
      String

    dimensionLawText :
      String

    dimensionWitnessRef :
      String

    dimensionRouteNamed :
      Bool

    dimensionRouteNamedIsTrue :
      dimensionRouteNamed ≡ true

    authorityPayloadSupplied :
      Bool

    authorityPayloadSuppliedIsFalse :
      authorityPayloadSupplied ≡ false

open DimensionalDependency public

record ConsumerRouteDependency : Set₁ where
  field
    routeLabel :
      String

    consumerTarget :
      ExactSIConsumerTarget

    consumerSurfaceRef :
      String

    sourceConstantRef :
      String

    downstreamObjectRef :
      String

    routeEquationText :
      String

    routeDependencyNamed :
      Bool

    routeDependencyNamedIsTrue :
      routeDependencyNamed ≡ true

    consumerIngestionReceiptPresent :
      Bool

    consumerIngestionReceiptPresentIsFalse :
      consumerIngestionReceiptPresent ≡ false

    downstreamPromotionEnabled :
      Bool

    downstreamPromotionEnabledIsFalse :
      downstreamPromotionEnabled ≡ false

open ConsumerRouteDependency public

record ConsumerIngestionPromotionGuard : Set₁ where
  field
    guardLabel :
      String

    parsedManifest :
      Parsed.SIExactConstantParsedCarrierRequestManifest

    authorityManifest :
      Artifact.SIDefiningConstantsAuthorityArtifactRequestManifest

    authorityArtifactPresent :
      Bool

    authorityArtifactPresentIsFalse :
      authorityArtifactPresent ≡ false

    acceptedAuthorityTokenPresent :
      Bool

    acceptedAuthorityTokenPresentIsFalse :
      acceptedAuthorityTokenPresent ≡ false

    consumerIngestionReceiptPresent :
      Bool

    consumerIngestionReceiptPresentIsFalse :
      consumerIngestionReceiptPresent ≡ false

    numericValuePromoted :
      Bool

    numericValuePromotedIsFalse :
      numericValuePromoted ≡ false

    downstreamConsumerPromotion :
      Bool

    downstreamConsumerPromotionIsFalse :
      downstreamConsumerPromotion ≡ false

open ConsumerIngestionPromotionGuard public

record ExactSIConsumerIngestionBridgeRow : Set₁ where
  field
    rowLabel :
      String

    consumerTarget :
      ExactSIConsumerTarget

    payloadText :
      ConsumerIngestionPayloadText

    parsedCarrierDependency :
      ParsedCarrierDependency

    dimensionalDependency :
      DimensionalDependency

    consumerRouteDependency :
      ConsumerRouteDependency

    promotionGuard :
      ConsumerIngestionPromotionGuard

    constantSymbolMatchesPayload :
      ConsumerIngestionPayloadText.consumerTarget payloadText
      ≡
      consumerTarget

    targetMatchesRoute :
      ConsumerRouteDependency.consumerTarget consumerRouteDependency
      ≡
      consumerTarget

    ingestionReceiptStillFalse :
      ConsumerIngestionPromotionGuard.consumerIngestionReceiptPresent
        promotionGuard
      ≡
      false

    numericPromotionStillFalse :
      ConsumerIngestionPromotionGuard.numericValuePromoted promotionGuard
      ≡
      false

open ExactSIConsumerIngestionBridgeRow public

cs133PayloadText : ConsumerIngestionPayloadText
cs133PayloadText =
  record
    { constantSymbol =
        "Delta nu Cs"
    ; consumerTarget =
        cs133SISecondRouteTarget
    ; parsedCarrierRowRef =
        "DASHI.Promotion.SIExactConstantParsedCarrierRequest.canonicalDeltaNuCsParsedCarrierRowRequest"
    ; rawAuthorityText =
        Parsed.rawAuthorityText Parsed.canonicalDeltaNuCsParsedCarrierRowRequest
    ; parsedCarrierText =
        "9192631770 natural-number carrier, with raw text 9 192 631 770"
    ; unitConventionText =
        "Hz"
    ; dimensionalDependencyText =
        "Hz = s^-1; 9192631770 periods define one SI second"
    ; consumerRouteDependencyText =
        "DASHI.Physics.Closure.AtomicClockSISecondCalibrationBridge.natToSISecondCalibrationRoute"
    ; authorityWallText =
        "consumer ingestion remains false until BIPM/NIST artifact evidence and authority token are supplied"
    }

cPayloadText : ConsumerIngestionPayloadText
cPayloadText =
  record
    { constantSymbol =
        "c"
    ; consumerTarget =
        speedOfLightMetreRouteTarget
    ; parsedCarrierRowRef =
        "DASHI.Promotion.SIExactConstantParsedCarrierRequest.canonicalCParsedCarrierRowRequest"
    ; rawAuthorityText =
        Parsed.rawAuthorityText Parsed.canonicalCParsedCarrierRowRequest
    ; parsedCarrierText =
        "299792458 natural-number carrier, with raw text 299 792 458"
    ; unitConventionText =
        "m s^-1"
    ; dimensionalDependencyText =
        "metre = c * second / 299792458"
    ; consumerRouteDependencyText =
        "DASHI.Promotion.SIMetreFromSecondAndCAdapter.canonicalSIMetreFromSecondAndCAdapter"
    ; authorityWallText =
        "metre route is named, but c artifact acceptance and spectroscopy promotion remain false"
    }

hPayloadText : ConsumerIngestionPayloadText
hPayloadText =
  record
    { constantSymbol =
        "h"
    ; consumerTarget =
        planckHbarStoneRouteTarget
    ; parsedCarrierRowRef =
        "DASHI.Promotion.SIExactConstantParsedCarrierRequest.canonicalHParsedCarrierRowRequest"
    ; rawAuthorityText =
        Parsed.rawAuthorityText Parsed.canonicalHParsedCarrierRowRequest
    ; parsedCarrierText =
        "6.62607015e-34 exact decimal/scientific carrier represented without floats"
    ; unitConventionText =
        "J s"
    ; dimensionalDependencyText =
        "hbar = h / (2 pi); dim hbar = kg m^2 s^-1"
    ; consumerRouteDependencyText =
        "DASHI.Promotion.PlanckHbarSIPayloadRequest and DASHI.Physics.Closure.StoneSISecondTimeParameterBridge"
    ; authorityWallText =
        "hbar/Stone consumption remains false until h authority payload and physical Stone inputs are supplied"
    }

cs133ParsedCarrierDependency : ParsedCarrierDependency
cs133ParsedCarrierDependency =
  mkParsedCarrierDependency
    "Delta nu Cs parsed carrier consumed by SI second route"
    Parsed.canonicalDeltaNuCsParsedCarrierRowRequest

cParsedCarrierDependency : ParsedCarrierDependency
cParsedCarrierDependency =
  mkParsedCarrierDependency
    "c parsed carrier consumed by metre adapter"
    Parsed.canonicalCParsedCarrierRowRequest

hParsedCarrierDependency : ParsedCarrierDependency
hParsedCarrierDependency =
  mkParsedCarrierDependency
    "h parsed carrier consumed by hbar/Stone request"
    Parsed.canonicalHParsedCarrierRowRequest

cs133DimensionalDependency : DimensionalDependency
cs133DimensionalDependency =
  record
    { dimensionLabel =
        "Cs-133 frequency-to-second dimensional route"
    ; unitText =
        "Hz"
    ; sourceDimensionRef =
        "DASHI.Physics.Closure.AtomicClockSISecondCalibrationBridge.siHertzDimension"
    ; consumerDimensionRef =
        "DASHI.Physics.Closure.AtomicClockSISecondCalibrationBridge.siSecondDimension"
    ; dimensionLawText =
        "Hz has time exponent -1; one second is the inverse-period count fixed by Delta nu Cs"
    ; dimensionWitnessRef =
        "DASHI.Physics.Closure.AtomicClockSISecondCalibrationBridge.canonicalCs133SISecondAnchor"
    ; dimensionRouteNamed =
        true
    ; dimensionRouteNamedIsTrue =
        refl
    ; authorityPayloadSupplied =
        false
    ; authorityPayloadSuppliedIsFalse =
        refl
    }

cDimensionalDependency : DimensionalDependency
cDimensionalDependency =
  record
    { dimensionLabel =
        "speed-of-light second-to-metre dimensional route"
    ; unitText =
        "m s^-1"
    ; sourceDimensionRef =
        "DASHI.Promotion.SIMetreFromSecondAndCAdapter.speedOfLightUnitDimensionRoute"
    ; consumerDimensionRef =
        "DASHI.Promotion.SIMetreFromSecondAndCAdapter.metreUnitDimensionRoute"
    ; dimensionLawText =
        "dim(c * second) = length, so metre is derived from the exact c integer and SI second"
    ; dimensionWitnessRef =
        "DASHI.Promotion.SIMetreFromSecondAndCAdapter.canonicalAdapterMetreLengthExponentIsPlusOne"
    ; dimensionRouteNamed =
        true
    ; dimensionRouteNamedIsTrue =
        refl
    ; authorityPayloadSupplied =
        false
    ; authorityPayloadSuppliedIsFalse =
        refl
    }

hDimensionalDependency : DimensionalDependency
hDimensionalDependency =
  record
    { dimensionLabel =
        "Planck-h to hbar Stone dimensional route"
    ; unitText =
        "J s"
    ; sourceDimensionRef =
        "DASHI.Promotion.PlanckHbarSIPayloadRequest.canonicalPlanckDimensionShape"
    ; consumerDimensionRef =
        "DASHI.Physics.Closure.StoneSISecondTimeParameterBridge.canonicalStoneSISecondTimeParameterBridge"
    ; dimensionLawText =
        "hbar = h / (2 pi), with 2 pi dimensionless, so hbar has the same J s dimension as h"
    ; dimensionWitnessRef =
        "DASHI.Promotion.PlanckHbarSIPayloadRequest.canonicalPlanckDimensionVectorTextIsJouleSecondShape"
    ; dimensionRouteNamed =
        true
    ; dimensionRouteNamedIsTrue =
        refl
    ; authorityPayloadSupplied =
        Planck.hbarAuthorityPayloadSupplied
    ; authorityPayloadSuppliedIsFalse =
        Planck.hbarAuthorityPayloadSuppliedIsFalse
    }

cs133ConsumerRouteDependency : ConsumerRouteDependency
cs133ConsumerRouteDependency =
  record
    { routeLabel =
        "Delta nu Cs -> natToSISecondCalibrationRoute"
    ; consumerTarget =
        cs133SISecondRouteTarget
    ; consumerSurfaceRef =
        "DASHI.Physics.Closure.AtomicClockSISecondCalibrationBridge"
    ; sourceConstantRef =
        "DASHI.Promotion.SIExactConstantParsedCarrierRequest.canonicalDeltaNuCsNaturalCarrier"
    ; downstreamObjectRef =
        "natToSISecondCalibrationRoute : Nat -> SITimeFrequencyUnit"
    ; routeEquationText =
        "n Cs-133 periods map to SI second carrier through n / 9192631770 seconds"
    ; routeDependencyNamed =
        true
    ; routeDependencyNamedIsTrue =
        refl
    ; consumerIngestionReceiptPresent =
        false
    ; consumerIngestionReceiptPresentIsFalse =
        refl
    ; downstreamPromotionEnabled =
        false
    ; downstreamPromotionEnabledIsFalse =
        refl
    }

cConsumerRouteDependency : ConsumerRouteDependency
cConsumerRouteDependency =
  record
    { routeLabel =
        "c -> SIMetreFromSecondAndCAdapter"
    ; consumerTarget =
        speedOfLightMetreRouteTarget
    ; consumerSurfaceRef =
        "DASHI.Promotion.SIMetreFromSecondAndCAdapter"
    ; sourceConstantRef =
        "DASHI.Promotion.SIExactConstantParsedCarrierRequest.canonicalCMetrePerSecondIntegerCarrier"
    ; downstreamObjectRef =
        "canonicalSIMetreFromSecondAndCAdapter"
    ; routeEquationText =
        "metre = c * second / 299792458"
    ; routeDependencyNamed =
        true
    ; routeDependencyNamedIsTrue =
        refl
    ; consumerIngestionReceiptPresent =
        false
    ; consumerIngestionReceiptPresentIsFalse =
        refl
    ; downstreamPromotionEnabled =
        Metre.SIMetreFromSecondAndCAdapter.authorityPayloadPromoted
          Metre.canonicalSIMetreFromSecondAndCAdapter
    ; downstreamPromotionEnabledIsFalse =
        Metre.canonicalAdapterAuthorityPayloadPromotedIsFalse
    }

hConsumerRouteDependency : ConsumerRouteDependency
hConsumerRouteDependency =
  record
    { routeLabel =
        "h -> hbar request -> Stone Schrodinger bridge"
    ; consumerTarget =
        planckHbarStoneRouteTarget
    ; consumerSurfaceRef =
        "DASHI.Promotion.PlanckHbarSIPayloadRequest"
    ; sourceConstantRef =
        "DASHI.Promotion.SIExactConstantParsedCarrierRequest.canonicalHScientificDecimalCarrier"
    ; downstreamObjectRef =
        "DASHI.Physics.Closure.StoneSISecondTimeParameterBridge.canonicalStoneSISecondTimeParameterBridge"
    ; routeEquationText =
        "hbar = h / (2 pi), consumed by U(t) = exp(-i H t / hbar)"
    ; routeDependencyNamed =
        true
    ; routeDependencyNamedIsTrue =
        refl
    ; consumerIngestionReceiptPresent =
        false
    ; consumerIngestionReceiptPresentIsFalse =
        refl
    ; downstreamPromotionEnabled =
        false
    ; downstreamPromotionEnabledIsFalse =
        refl
    }

mkPromotionGuard :
  String →
  (downstream : Bool) →
  downstream ≡ false →
  ConsumerIngestionPromotionGuard
mkPromotionGuard label downstream downstreamFalse =
  record
    { guardLabel =
        label
    ; parsedManifest =
        Parsed.canonicalSIExactConstantParsedCarrierRequestManifest
    ; authorityManifest =
        Artifact.canonicalSIDefiningConstantsAuthorityArtifactRequestManifest
    ; authorityArtifactPresent =
        Parsed.SIExactConstantParsedCarrierRequestManifest.authorityArtifactPresent
          Parsed.canonicalSIExactConstantParsedCarrierRequestManifest
    ; authorityArtifactPresentIsFalse =
        Parsed.SIExactConstantParsedCarrierRequestManifest.authorityArtifactPresentIsFalse
          Parsed.canonicalSIExactConstantParsedCarrierRequestManifest
    ; acceptedAuthorityTokenPresent =
        Parsed.SIExactConstantParsedCarrierRequestManifest.acceptedAuthorityTokenPresent
          Parsed.canonicalSIExactConstantParsedCarrierRequestManifest
    ; acceptedAuthorityTokenPresentIsFalse =
        Parsed.SIExactConstantParsedCarrierRequestManifest.acceptedAuthorityTokenPresentIsFalse
          Parsed.canonicalSIExactConstantParsedCarrierRequestManifest
    ; consumerIngestionReceiptPresent =
        Parsed.SIExactConstantParsedCarrierRequestManifest.consumerIngestionReceiptPresent
          Parsed.canonicalSIExactConstantParsedCarrierRequestManifest
    ; consumerIngestionReceiptPresentIsFalse =
        Parsed.SIExactConstantParsedCarrierRequestManifest.consumerIngestionReceiptPresentIsFalse
          Parsed.canonicalSIExactConstantParsedCarrierRequestManifest
    ; numericValuePromoted =
        Parsed.SIExactConstantParsedCarrierRequestManifest.anyNumericValuePromoted
          Parsed.canonicalSIExactConstantParsedCarrierRequestManifest
    ; numericValuePromotedIsFalse =
        Parsed.SIExactConstantParsedCarrierRequestManifest.anyNumericValuePromotedIsFalse
          Parsed.canonicalSIExactConstantParsedCarrierRequestManifest
    ; downstreamConsumerPromotion =
        downstream
    ; downstreamConsumerPromotionIsFalse =
        downstreamFalse
    }

cs133PromotionGuard : ConsumerIngestionPromotionGuard
cs133PromotionGuard =
  mkPromotionGuard
    "Delta nu Cs consumer ingestion remains fail-closed"
    false
    refl

cPromotionGuard : ConsumerIngestionPromotionGuard
cPromotionGuard =
  mkPromotionGuard
    "c consumer ingestion and metre authority promotion remain fail-closed"
    (Metre.SIMetreFromSecondAndCAdapter.authorityPayloadPromoted
      Metre.canonicalSIMetreFromSecondAndCAdapter)
    Metre.canonicalAdapterAuthorityPayloadPromotedIsFalse

hPromotionGuard : ConsumerIngestionPromotionGuard
hPromotionGuard =
  mkPromotionGuard
    "h consumer ingestion and physical Stone promotion remain fail-closed"
    false
    refl

canonicalDeltaNuCsConsumerIngestionBridgeRow :
  ExactSIConsumerIngestionBridgeRow
canonicalDeltaNuCsConsumerIngestionBridgeRow =
  record
    { rowLabel =
        "Delta nu Cs parsed carrier to atomic-clock SI second consumer"
    ; consumerTarget =
        cs133SISecondRouteTarget
    ; payloadText =
        cs133PayloadText
    ; parsedCarrierDependency =
        cs133ParsedCarrierDependency
    ; dimensionalDependency =
        cs133DimensionalDependency
    ; consumerRouteDependency =
        cs133ConsumerRouteDependency
    ; promotionGuard =
        cs133PromotionGuard
    ; constantSymbolMatchesPayload =
        refl
    ; targetMatchesRoute =
        refl
    ; ingestionReceiptStillFalse =
        refl
    ; numericPromotionStillFalse =
        refl
    }

canonicalCConsumerIngestionBridgeRow :
  ExactSIConsumerIngestionBridgeRow
canonicalCConsumerIngestionBridgeRow =
  record
    { rowLabel =
        "c parsed carrier to metre-from-second adapter consumer"
    ; consumerTarget =
        speedOfLightMetreRouteTarget
    ; payloadText =
        cPayloadText
    ; parsedCarrierDependency =
        cParsedCarrierDependency
    ; dimensionalDependency =
        cDimensionalDependency
    ; consumerRouteDependency =
        cConsumerRouteDependency
    ; promotionGuard =
        cPromotionGuard
    ; constantSymbolMatchesPayload =
        refl
    ; targetMatchesRoute =
        refl
    ; ingestionReceiptStillFalse =
        refl
    ; numericPromotionStillFalse =
        refl
    }

canonicalHConsumerIngestionBridgeRow :
  ExactSIConsumerIngestionBridgeRow
canonicalHConsumerIngestionBridgeRow =
  record
    { rowLabel =
        "h parsed carrier to hbar/Stone consumer"
    ; consumerTarget =
        planckHbarStoneRouteTarget
    ; payloadText =
        hPayloadText
    ; parsedCarrierDependency =
        hParsedCarrierDependency
    ; dimensionalDependency =
        hDimensionalDependency
    ; consumerRouteDependency =
        hConsumerRouteDependency
    ; promotionGuard =
        hPromotionGuard
    ; constantSymbolMatchesPayload =
        refl
    ; targetMatchesRoute =
        refl
    ; ingestionReceiptStillFalse =
        refl
    ; numericPromotionStillFalse =
        refl
    }

record SIExactConstantConsumerIngestionBridge : Set₁ where
  field
    bridgeLabel :
      String

    sourceParsedManifest :
      Parsed.SIExactConstantParsedCarrierRequestManifest

    sourceArtifactManifest :
      Artifact.SIDefiningConstantsAuthorityArtifactRequestManifest

    consumerRows :
      List ExactSIConsumerIngestionBridgeRow

    consumerRowCount :
      Nat

    consumerRowCountIs3 :
      consumerRowCount ≡ 3

    payloadTextKeys :
      List ConsumerIngestionPayloadTextKey

    payloadTextKeyCount :
      Nat

    payloadTextKeyCountIs8 :
      payloadTextKeyCount ≡ 8

    deltaNuCsRow :
      ExactSIConsumerIngestionBridgeRow

    cRow :
      ExactSIConsumerIngestionBridgeRow

    hRow :
      ExactSIConsumerIngestionBridgeRow

    routePolicyText :
      String

    authorityPolicyText :
      String

    anyConsumerIngestionReceiptPresent :
      Bool

    anyConsumerIngestionReceiptPresentIsFalse :
      anyConsumerIngestionReceiptPresent ≡ false

    anyNumericValuePromoted :
      Bool

    anyNumericValuePromotedIsFalse :
      anyNumericValuePromoted ≡ false

    anyDownstreamPromotionEnabled :
      Bool

    anyDownstreamPromotionEnabledIsFalse :
      anyDownstreamPromotionEnabled ≡ false

open SIExactConstantConsumerIngestionBridge public

canonicalConsumerRows : List ExactSIConsumerIngestionBridgeRow
canonicalConsumerRows =
  canonicalDeltaNuCsConsumerIngestionBridgeRow
  ∷ canonicalCConsumerIngestionBridgeRow
  ∷ canonicalHConsumerIngestionBridgeRow
  ∷ []

canonicalSIExactConstantConsumerIngestionBridge :
  SIExactConstantConsumerIngestionBridge
canonicalSIExactConstantConsumerIngestionBridge =
  record
    { bridgeLabel =
        "Exact SI parsed constants consumer-ingestion bridge"
    ; sourceParsedManifest =
        Parsed.canonicalSIExactConstantParsedCarrierRequestManifest
    ; sourceArtifactManifest =
        Artifact.canonicalSIDefiningConstantsAuthorityArtifactRequestManifest
    ; consumerRows =
        canonicalConsumerRows
    ; consumerRowCount =
        3
    ; consumerRowCountIs3 =
        refl
    ; payloadTextKeys =
        canonicalConsumerIngestionPayloadTextKeys
    ; payloadTextKeyCount =
        8
    ; payloadTextKeyCountIs8 =
        refl
    ; deltaNuCsRow =
        canonicalDeltaNuCsConsumerIngestionBridgeRow
    ; cRow =
        canonicalCConsumerIngestionBridgeRow
    ; hRow =
        canonicalHConsumerIngestionBridgeRow
    ; routePolicyText =
        "every exact SI parsed carrier names exactly one downstream consumer route"
    ; authorityPolicyText =
        "consumer-route naming is not artifact acceptance, consumer ingestion, or numeric promotion"
    ; anyConsumerIngestionReceiptPresent =
        false
    ; anyConsumerIngestionReceiptPresentIsFalse =
        refl
    ; anyNumericValuePromoted =
        false
    ; anyNumericValuePromotedIsFalse =
        refl
    ; anyDownstreamPromotionEnabled =
        false
    ; anyDownstreamPromotionEnabledIsFalse =
        refl
    }

canonicalDeltaNuCsBridgeUsesCs133Target :
  ExactSIConsumerIngestionBridgeRow.consumerTarget
    canonicalDeltaNuCsConsumerIngestionBridgeRow
  ≡
  cs133SISecondRouteTarget
canonicalDeltaNuCsBridgeUsesCs133Target =
  refl

canonicalCBridgeUsesMetreTarget :
  ExactSIConsumerIngestionBridgeRow.consumerTarget
    canonicalCConsumerIngestionBridgeRow
  ≡
  speedOfLightMetreRouteTarget
canonicalCBridgeUsesMetreTarget =
  refl

canonicalHBridgeUsesHbarStoneTarget :
  ExactSIConsumerIngestionBridgeRow.consumerTarget
    canonicalHConsumerIngestionBridgeRow
  ≡
  planckHbarStoneRouteTarget
canonicalHBridgeUsesHbarStoneTarget =
  refl

canonicalDeltaNuCsParsedIntegerFeedsAtomicAnchor :
  Parsed.ExactIntegerTextCarrier.absoluteValue
    Parsed.canonicalDeltaNuCsNaturalCarrier
  ≡
  Atomic.cs133ExactInteger
canonicalDeltaNuCsParsedIntegerFeedsAtomicAnchor =
  refl

canonicalCParsedIntegerFeedsMetreAdapter :
  Parsed.ExactIntegerTextCarrier.absoluteValue
    Parsed.canonicalCMetrePerSecondIntegerCarrier
  ≡
  Metre.speedOfLightExactInteger
canonicalCParsedIntegerFeedsMetreAdapter =
  refl

canonicalHParsedUnitFeedsPlanckRequest :
  Parsed.ExactScientificDecimalCarrier.unitText
    Parsed.canonicalHScientificDecimalCarrier
  ≡
  Planck.PlanckHbarSIPayloadRequest.planckUnitConvention
    Planck.canonicalPlanckHbarSIPayloadRequest
canonicalHParsedUnitFeedsPlanckRequest =
  refl

canonicalConsumerBridgeKeepsIngestionFalse :
  SIExactConstantConsumerIngestionBridge.anyConsumerIngestionReceiptPresent
    canonicalSIExactConstantConsumerIngestionBridge
  ≡
  false
canonicalConsumerBridgeKeepsIngestionFalse =
  refl

canonicalConsumerBridgeKeepsNumericPromotionFalse :
  SIExactConstantConsumerIngestionBridge.anyNumericValuePromoted
    canonicalSIExactConstantConsumerIngestionBridge
  ≡
  false
canonicalConsumerBridgeKeepsNumericPromotionFalse =
  refl

canonicalConsumerBridgeKeepsDownstreamPromotionFalse :
  SIExactConstantConsumerIngestionBridge.anyDownstreamPromotionEnabled
    canonicalSIExactConstantConsumerIngestionBridge
  ≡
  false
canonicalConsumerBridgeKeepsDownstreamPromotionFalse =
  refl
