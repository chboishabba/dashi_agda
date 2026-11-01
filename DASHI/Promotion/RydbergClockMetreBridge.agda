module DASHI.Promotion.RydbergClockMetreBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Constants.Registry as Registry
import DASHI.Promotion.ChemistryAuthorityBinding as Chemistry
import DASHI.Promotion.NumericMeasuredAuthorityTokenNormalization as Tokens

------------------------------------------------------------------------
-- SI clock/metre bridge for the Rydberg spectroscopy lane.
--
-- The exact SI clock and speed-of-light facts are enough to request the
-- metre as a derived unit carrier.  They are not enough to ingest a Rydberg
-- value, accept an isotope/reduced-mass convention, accept a NIST ASD line,
-- or promote a chemistry/spectroscopy claim.

data DimensionExponent : Set where
  minusOne : DimensionExponent
  zero : DimensionExponent
  plusOne : DimensionExponent

exponentText : DimensionExponent → String
exponentText minusOne = "-1"
exponentText zero = "0"
exponentText plusOne = "+1"

record DimensionVectorRoute : Set₁ where
  field
    routeLabel : String
    symbolLabel : String
    canonicalUnit : String
    lengthExponent : DimensionExponent
    timeExponent : DimensionExponent
    massExponent : DimensionExponent
    amountExponent : DimensionExponent
    routeExpression : String
    authorityBoundary : String

open DimensionVectorRoute public

mkDimensionRoute :
  String →
  String →
  String →
  DimensionExponent →
  DimensionExponent →
  String →
  String →
  DimensionVectorRoute
mkDimensionRoute label symbol unit length time expression boundary =
  record
    { routeLabel = label
    ; symbolLabel = symbol
    ; canonicalUnit = unit
    ; lengthExponent = length
    ; timeExponent = time
    ; massExponent = zero
    ; amountExponent = zero
    ; routeExpression = expression
    ; authorityBoundary = boundary
    }

secondDimensionRoute : DimensionVectorRoute
secondDimensionRoute =
  mkDimensionRoute
    "SI second base-unit dimension route"
    "s"
    "second"
    zero
    plusOne
    "Delta nu Cs fixes the second; time exponent is +1"
    "exact SI prerequisite only"

hertzDimensionRoute : DimensionVectorRoute
hertzDimensionRoute =
  mkDimensionRoute
    "hertz frequency dimension route"
    "Hz"
    "s^-1"
    zero
    minusOne
    "Hz = s^-1; time exponent is -1"
    "exact derived unit only"

metreDimensionRoute : DimensionVectorRoute
metreDimensionRoute =
  mkDimensionRoute
    "metre derived from exact clock and light-speed route"
    "m"
    "m"
    plusOne
    zero
    "m = c * s / 299792458, with c exact in m s^-1"
    "derived-unit request; no spectral authority accepted"

wavenumberDimensionRoute : DimensionVectorRoute
wavenumberDimensionRoute =
  mkDimensionRoute
    "wavenumber and R_infinity dimension route"
    "R_infinity"
    "m^-1"
    minusOne
    zero
    "wavenumber = 1 / lambda; R_infinity has length exponent -1"
    "measured CODATA payload still required"

canonicalDimensionVectorRoutes : List DimensionVectorRoute
canonicalDimensionVectorRoutes =
  secondDimensionRoute
  ∷ hertzDimensionRoute
  ∷ metreDimensionRoute
  ∷ wavenumberDimensionRoute
  ∷ []

record ExactPrerequisite : Set₁ where
  field
    prerequisiteLabel : String
    registrySlot : String
    authorityClass : Registry.ConstantAuthorityClass
    exactBySIDefinition : Bool
    exactBySIDefinitionIsTrue : exactBySIDefinition ≡ true
    consumedForMetreRoute : Bool
    consumedForMetreRouteIsTrue : consumedForMetreRoute ≡ true
    promotesSpectroscopy : Bool
    promotesSpectroscopyIsFalse : promotesSpectroscopy ≡ false

open ExactPrerequisite public

csSecondPrerequisite : ExactPrerequisite
csSecondPrerequisite = record
  { prerequisiteLabel = "caesium-133 hyperfine transition frequency"
  ; registrySlot =
      "DASHI.Constants.Registry.canonicalSIDefiningConstants.Delta nu Cs"
  ; authorityClass = Registry.exactSIDefiningConstant
  ; exactBySIDefinition = true
  ; exactBySIDefinitionIsTrue = refl
  ; consumedForMetreRoute = true
  ; consumedForMetreRouteIsTrue = refl
  ; promotesSpectroscopy = false
  ; promotesSpectroscopyIsFalse = refl
  }

speedOfLightPrerequisite : ExactPrerequisite
speedOfLightPrerequisite = record
  { prerequisiteLabel = "speed of light in vacuum"
  ; registrySlot =
      "DASHI.Constants.Registry.canonicalSIDefiningConstants.c"
  ; authorityClass = Registry.exactSIDefiningConstant
  ; exactBySIDefinition = true
  ; exactBySIDefinitionIsTrue = refl
  ; consumedForMetreRoute = true
  ; consumedForMetreRouteIsTrue = refl
  ; promotesSpectroscopy = false
  ; promotesSpectroscopyIsFalse = refl
  }

record DerivedUnitRequest : Set₁ where
  field
    requestLabel : String
    requestedUnit : String
    requestedFrom : List String
    exactDerivedConstantClass : Registry.ConstantAuthorityClass
    dimensionRoute : DimensionVectorRoute
    requestAccepted : Bool
    requestAcceptedIsFalse : requestAccepted ≡ false
    requiresExternalPayload : Bool
    requiresExternalPayloadIsTrue :
      requiresExternalPayload ≡ true

open DerivedUnitRequest public

metreDerivedUnitRequest : DerivedUnitRequest
metreDerivedUnitRequest = record
  { requestLabel =
      "metre carrier request from SI second and exact speed of light"
  ; requestedUnit = "m"
  ; requestedFrom =
      "Delta nu Cs exact second prerequisite"
      ∷ "c exact speed-of-light prerequisite"
      ∷ []
  ; exactDerivedConstantClass = Registry.exactSIDerivedConstant
  ; dimensionRoute = metreDimensionRoute
  ; requestAccepted = false
  ; requestAcceptedIsFalse = refl
  ; requiresExternalPayload = true
  ; requiresExternalPayloadIsTrue = refl
  }

record RydbergClockMetreBridge : Set₁ where
  field
    bridgeLabel : String
    sourceRegistry : Registry.ConstantsRegistry
    chemistryAuthorityBinding :
      Chemistry.ChemistryAuthorityBinding
    normalizedRydbergAuthorityToken :
      Tokens.NormalizedMeasuredAuthorityToken
    csSecondPrerequisiteField : ExactPrerequisite
    speedOfLightPrerequisiteField : ExactPrerequisite
    metreDerivedUnitRequestField : DerivedUnitRequest
    dimensionVectorRoutes : List DimensionVectorRoute
    secondRoute : DimensionVectorRoute
    hertzRoute : DimensionVectorRoute
    metreRoute : DimensionVectorRoute
    wavenumberRoute : DimensionVectorRoute
    symbolicRydbergFormula : String
    rInfinityCODATAMeasuredPayloadStillRequired : Bool
    rInfinityCODATAMeasuredPayloadStillRequiredIsTrue :
      rInfinityCODATAMeasuredPayloadStillRequired ≡ true
    isotopeReducedMassAdapterStillRequired : Bool
    isotopeReducedMassAdapterStillRequiredIsTrue :
      isotopeReducedMassAdapterStillRequired ≡ true
    nistASDSpectralLineTokenStillRequired : Bool
    nistASDSpectralLineTokenStillRequiredIsTrue :
      nistASDSpectralLineTokenStillRequired ≡ true
    chemistryPromotion : Bool
    chemistryPromotionIsFalse : chemistryPromotion ≡ false
    spectroscopyPromotion : Bool
    spectroscopyPromotionIsFalse : spectroscopyPromotion ≡ false
    acceptedAuthorityTokenPresent : Bool
    acceptedAuthorityTokenPresentIsFalse :
      acceptedAuthorityTokenPresent ≡ false
    numericValueLoaded : Bool
    numericValueLoadedIsFalse : numericValueLoaded ≡ false
    metreRouteOnly : Bool
    metreRouteOnlyIsTrue : metreRouteOnly ≡ true
    falseBridgeGuard : Bool
    falseBridgeGuardIsTrue : falseBridgeGuard ≡ true

open RydbergClockMetreBridge public

canonicalRydbergClockMetreBridge : RydbergClockMetreBridge
canonicalRydbergClockMetreBridge = record
  { bridgeLabel =
      "Rydberg lane SI clock-to-metre fail-closed authority bridge"
  ; sourceRegistry = Registry.repoWideConstantsRegistry
  ; chemistryAuthorityBinding =
      Chemistry.canonicalChemistryAuthorityBinding
  ; normalizedRydbergAuthorityToken =
      Tokens.rydbergNormalizedToken
  ; csSecondPrerequisiteField = csSecondPrerequisite
  ; speedOfLightPrerequisiteField = speedOfLightPrerequisite
  ; metreDerivedUnitRequestField = metreDerivedUnitRequest
  ; dimensionVectorRoutes = canonicalDimensionVectorRoutes
  ; secondRoute = secondDimensionRoute
  ; hertzRoute = hertzDimensionRoute
  ; metreRoute = metreDimensionRoute
  ; wavenumberRoute = wavenumberDimensionRoute
  ; symbolicRydbergFormula =
      "Rydberg formula: 1 / lambda = R_infinity (1 / n_lower^2 - 1 / n_upper^2)"
  ; rInfinityCODATAMeasuredPayloadStillRequired = true
  ; rInfinityCODATAMeasuredPayloadStillRequiredIsTrue = refl
  ; isotopeReducedMassAdapterStillRequired = true
  ; isotopeReducedMassAdapterStillRequiredIsTrue = refl
  ; nistASDSpectralLineTokenStillRequired = true
  ; nistASDSpectralLineTokenStillRequiredIsTrue = refl
  ; chemistryPromotion =
      Chemistry.physicalChemistryPromoted
        Chemistry.canonicalChemistryAuthorityBinding
  ; chemistryPromotionIsFalse =
      Chemistry.canonicalAuthorityBindingPhysicalChemistryPromotionIsFalse
  ; spectroscopyPromotion =
      Chemistry.spectroscopyPromoted
        Chemistry.canonicalChemistryAuthorityBinding
  ; spectroscopyPromotionIsFalse =
      Chemistry.canonicalAuthorityBindingSpectroscopyPromotionIsFalse
  ; acceptedAuthorityTokenPresent =
      Chemistry.acceptedAuthorityTokenPresent
        Chemistry.canonicalChemistryAuthorityBinding
  ; acceptedAuthorityTokenPresentIsFalse =
      Chemistry.canonicalAuthorityTokenStillMissing
  ; numericValueLoaded =
      Tokens.numericValueLoaded Tokens.rydbergNormalizedToken
  ; numericValueLoadedIsFalse =
      Tokens.numericValueLoadedIsFalse Tokens.rydbergNormalizedToken
  ; metreRouteOnly = true
  ; metreRouteOnlyIsTrue = refl
  ; falseBridgeGuard = true
  ; falseBridgeGuardIsTrue = refl
  }

canonicalBridgeChemistryPromotionIsFalse :
  chemistryPromotion canonicalRydbergClockMetreBridge ≡ false
canonicalBridgeChemistryPromotionIsFalse =
  Chemistry.canonicalAuthorityBindingPhysicalChemistryPromotionIsFalse

canonicalBridgeSpectroscopyPromotionIsFalse :
  spectroscopyPromotion canonicalRydbergClockMetreBridge ≡ false
canonicalBridgeSpectroscopyPromotionIsFalse =
  Chemistry.canonicalAuthorityBindingSpectroscopyPromotionIsFalse

canonicalBridgeAuthorityTokenStillMissing :
  acceptedAuthorityTokenPresent canonicalRydbergClockMetreBridge ≡ false
canonicalBridgeAuthorityTokenStillMissing =
  Chemistry.canonicalAuthorityTokenStillMissing

canonicalBridgeRydbergNumericValueStillMissing :
  numericValueLoaded canonicalRydbergClockMetreBridge ≡ false
canonicalBridgeRydbergNumericValueStillMissing =
  Tokens.numericValueLoadedIsFalse Tokens.rydbergNormalizedToken

canonicalBridgeRydbergMeasuredPayloadStillRequired :
  rInfinityCODATAMeasuredPayloadStillRequired
    canonicalRydbergClockMetreBridge ≡ true
canonicalBridgeRydbergMeasuredPayloadStillRequired = refl

canonicalBridgeReducedMassAdapterStillRequired :
  isotopeReducedMassAdapterStillRequired
    canonicalRydbergClockMetreBridge ≡ true
canonicalBridgeReducedMassAdapterStillRequired = refl

canonicalBridgeNISTASDTokenStillRequired :
  nistASDSpectralLineTokenStillRequired
    canonicalRydbergClockMetreBridge ≡ true
canonicalBridgeNISTASDTokenStillRequired = refl

canonicalSecondTimeExponentIsPlusOne :
  timeExponent secondDimensionRoute ≡ plusOne
canonicalSecondTimeExponentIsPlusOne = refl

canonicalHertzTimeExponentIsMinusOne :
  timeExponent hertzDimensionRoute ≡ minusOne
canonicalHertzTimeExponentIsMinusOne = refl

canonicalMetreLengthExponentIsPlusOne :
  lengthExponent metreDimensionRoute ≡ plusOne
canonicalMetreLengthExponentIsPlusOne = refl

canonicalWavenumberLengthExponentIsMinusOne :
  lengthExponent wavenumberDimensionRoute ≡ minusOne
canonicalWavenumberLengthExponentIsMinusOne = refl
