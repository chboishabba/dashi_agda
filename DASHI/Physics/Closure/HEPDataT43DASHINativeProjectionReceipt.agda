module DASHI.Physics.Closure.HEPDataT43DASHINativeProjectionReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (lzero; Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Algebra.Trit using (Trit; neg; pos; zer)

import DASHI.Physics.DashiDynamics as DD
import DASHI.Physics.FascisticContractionInstance as FCI

------------------------------------------------------------------------
-- HEP-R36: DASHI-native sigma_DASHI t43 projection receipt request.
--
-- HEP-R35 records that no accepted DASHI-native t43 phi-star ratio API exists
-- here yet.  This module narrows that gap by recording the typed construction
-- surface requested for sigma_DASHI:
--   * DashiDynamics-backed source route,
--   * finite trit support,
--   * mass-window/depth binding for 50-76 over 76-106,
--   * phi-star projection law placeholder,
--   * lambda policy fixed before projection,
--   * no observed t43 ratio seeding,
--   * no comparison-law construction and no W3/W4/W5/W8 promotion.

data HEPDataT43DASHINativeProjectionStatus : Set where
  requestOnlyAwaitingDashiDynamicsBackedSigmaConstruction :
    HEPDataT43DASHINativeProjectionStatus

data SigmaDASHIConstructionRequirement : Set where
  requiresDashiDynamicsBackedSigmaSource :
    SigmaDASHIConstructionRequirement
  requiresFascisticContractionRouteBinding :
    SigmaDASHIConstructionRequirement
  requiresFiniteTritEnumeration :
    SigmaDASHIConstructionRequirement
  requiresMassDepthMap :
    SigmaDASHIConstructionRequirement
  requiresPhiStarProjectionLaw :
    SigmaDASHIConstructionRequirement
  requiresLambdaPolicy :
    SigmaDASHIConstructionRequirement
  requiresNoObservedRatioSeeding :
    SigmaDASHIConstructionRequirement
  requiresNonPromotionBoundary :
    SigmaDASHIConstructionRequirement

canonicalSigmaDASHIConstructionRequirements :
  List SigmaDASHIConstructionRequirement
canonicalSigmaDASHIConstructionRequirements =
  requiresDashiDynamicsBackedSigmaSource
  ∷ requiresFascisticContractionRouteBinding
  ∷ requiresFiniteTritEnumeration
  ∷ requiresMassDepthMap
  ∷ requiresPhiStarProjectionLaw
  ∷ requiresLambdaPolicy
  ∷ requiresNoObservedRatioSeeding
  ∷ requiresNonPromotionBoundary
  ∷ []

canonicalSigmaDASHITritEnumeration : List Trit
canonicalSigmaDASHITritEnumeration =
  neg ∷ zer ∷ pos ∷ []

data T43SigmaDASHIMassWindow : Set where
  massWindow50To76 :
    T43SigmaDASHIMassWindow
  massWindow76To106 :
    T43SigmaDASHIMassWindow

data T43SigmaDASHIMassRole : Set where
  ratioNumerator50To76 :
    T43SigmaDASHIMassRole
  ratioDenominator76To106 :
    T43SigmaDASHIMassRole

t43SigmaDASHIMassRole :
  T43SigmaDASHIMassWindow →
  T43SigmaDASHIMassRole
t43SigmaDASHIMassRole massWindow50To76 =
  ratioNumerator50To76
t43SigmaDASHIMassRole massWindow76To106 =
  ratioDenominator76To106

t43SigmaDASHIMassDepth :
  T43SigmaDASHIMassWindow →
  Nat
t43SigmaDASHIMassDepth massWindow50To76 =
  suc (suc zero)
t43SigmaDASHIMassDepth massWindow76To106 =
  suc (suc zero)

data T43PhiStarBinEndpoint : Set where
  phiStarLowEndpoint :
    T43PhiStarBinEndpoint
  phiStarHighEndpoint :
    T43PhiStarBinEndpoint

record T43PhiStarBinShape : Set where
  constructor mkT43PhiStarBinShape
  field
    binLabel :
      String

    endpointFields :
      List T43PhiStarBinEndpoint

    endpointFieldsAreCanonical :
      endpointFields
      ≡
      (phiStarLowEndpoint ∷ phiStarHighEndpoint ∷ [])

canonicalT43PhiStarBinShape : T43PhiStarBinShape
canonicalT43PhiStarBinShape =
  mkT43PhiStarBinShape
    "t43 phi-star bin with low/high endpoints"
    (phiStarLowEndpoint ∷ phiStarHighEndpoint ∷ [])
    refl

data SigmaDASHILambdaPolicy : Set where
  lambdaFixedBeforeProjection :
    SigmaDASHILambdaPolicy
  lambdaDerivedFromFiniteTritRoute :
    SigmaDASHILambdaPolicy
  lambdaNotTunedFromObservedT43Ratio :
    SigmaDASHILambdaPolicy
  lambdaFrozenBeforeComparisonLaw :
    SigmaDASHILambdaPolicy

canonicalSigmaDASHILambdaPolicy :
  List SigmaDASHILambdaPolicy
canonicalSigmaDASHILambdaPolicy =
  lambdaFixedBeforeProjection
  ∷ lambdaDerivedFromFiniteTritRoute
  ∷ lambdaNotTunedFromObservedT43Ratio
  ∷ lambdaFrozenBeforeComparisonLaw
  ∷ []

data SigmaDASHINativeProjectionBoundary : Set where
  noAcceptedSigmaDASHIProjectionReceiptHere :
    SigmaDASHINativeProjectionBoundary
  noObservedT43RatioBackfill :
    SigmaDASHINativeProjectionBoundary
  noProjectionCompleteClaim :
    SigmaDASHINativeProjectionBoundary
  noComparisonLawReceiptConstructed :
    SigmaDASHINativeProjectionBoundary
  noEmpiricalAdequacyClaim :
    SigmaDASHINativeProjectionBoundary
  noW3Promotion :
    SigmaDASHINativeProjectionBoundary
  noW4Promotion :
    SigmaDASHINativeProjectionBoundary
  noW5Promotion :
    SigmaDASHINativeProjectionBoundary
  noW8Promotion :
    SigmaDASHINativeProjectionBoundary

canonicalSigmaDASHINativeProjectionBoundaries :
  List SigmaDASHINativeProjectionBoundary
canonicalSigmaDASHINativeProjectionBoundaries =
  noAcceptedSigmaDASHIProjectionReceiptHere
  ∷ noObservedT43RatioBackfill
  ∷ noProjectionCompleteClaim
  ∷ noComparisonLawReceiptConstructed
  ∷ noEmpiricalAdequacyClaim
  ∷ noW3Promotion
  ∷ noW4Promotion
  ∷ noW5Promotion
  ∷ noW8Promotion
  ∷ []

data SigmaDASHIAcceptedProjectionReceipt : Set where

sigmaDASHIAcceptedProjectionReceiptImpossibleHere :
  SigmaDASHIAcceptedProjectionReceipt →
  ⊥
sigmaDASHIAcceptedProjectionReceiptImpossibleHere ()

record HEPDataT43DASHINativeProjectionReceiptRequestSurface : Setω where
  field
    status :
      HEPDataT43DASHINativeProjectionStatus

    constructionRequirements :
      List SigmaDASHIConstructionRequirement

    constructionRequirementsAreCanonical :
      constructionRequirements
      ≡
      canonicalSigmaDASHIConstructionRequirements

    dashiDynamicsBackedRoute :
      DD.DashiDynamics {lzero} {lzero} {lzero} {lzero} {lzero} Nat →
      SigmaDASHIConstructionRequirement

    dashiDynamicsBackedRouteIsSigmaSource :
      (dynamics :
        DD.DashiDynamics {lzero} {lzero} {lzero} {lzero} {lzero} Nat) →
      dashiDynamicsBackedRoute dynamics
      ≡
      requiresDashiDynamicsBackedSigmaSource

    fascisticContractionRoute :
      (n : Nat) →
      FCI.StrictFascisticMap n →
      SigmaDASHIConstructionRequirement

    fascisticContractionRouteIsBinding :
      (n : Nat) →
      (strictMap : FCI.StrictFascisticMap n) →
      fascisticContractionRoute n strictMap
      ≡
      requiresFascisticContractionRouteBinding

    finiteTritEnumeration :
      List Trit

    finiteTritEnumerationIsCanonical :
      finiteTritEnumeration
      ≡
      canonicalSigmaDASHITritEnumeration

    massDepthMap :
      T43SigmaDASHIMassWindow →
      Nat

    massDepthMapIsCanonical :
      (window : T43SigmaDASHIMassWindow) →
      massDepthMap window
      ≡
      t43SigmaDASHIMassDepth window

    massRoleMap :
      T43SigmaDASHIMassWindow →
      T43SigmaDASHIMassRole

    massRoleMapIsCanonical :
      (window : T43SigmaDASHIMassWindow) →
      massRoleMap window
      ≡
      t43SigmaDASHIMassRole window

    phiStarBinShape :
      T43PhiStarBinShape

    phiStarProjectionLaw :
      T43PhiStarBinShape →
      T43SigmaDASHIMassWindow →
      SigmaDASHIConstructionRequirement

    phiStarProjectionLawIsRequired :
      (bin : T43PhiStarBinShape) →
      (window : T43SigmaDASHIMassWindow) →
      phiStarProjectionLaw bin window
      ≡
      requiresPhiStarProjectionLaw

    lambdaPolicy :
      List SigmaDASHILambdaPolicy

    lambdaPolicyIsCanonical :
      lambdaPolicy
      ≡
      canonicalSigmaDASHILambdaPolicy

    observedT43RatiosMaySeedSigmaDASHI :
      Bool

    observedT43RatiosMaySeedSigmaDASHIIsFalse :
      observedT43RatiosMaySeedSigmaDASHI
      ≡
      false

    projectionReceiptConstructedHere :
      Bool

    projectionReceiptConstructedHereIsFalse :
      projectionReceiptConstructedHere
      ≡
      false

    comparisonLawReceiptConstructedHere :
      Bool

    comparisonLawReceiptConstructedHereIsFalse :
      comparisonLawReceiptConstructedHere
      ≡
      false

    w3PromotionConstructedHere :
      Bool

    w3PromotionConstructedHereIsFalse :
      w3PromotionConstructedHere
      ≡
      false

    w4PromotionConstructedHere :
      Bool

    w4PromotionConstructedHereIsFalse :
      w4PromotionConstructedHere
      ≡
      false

    w5PromotionConstructedHere :
      Bool

    w5PromotionConstructedHereIsFalse :
      w5PromotionConstructedHere
      ≡
      false

    w8PromotionConstructedHere :
      Bool

    w8PromotionConstructedHereIsFalse :
      w8PromotionConstructedHere
      ≡
      false

    requestedConstructionRoute :
      List String

    providerRequestFields :
      List String

    nonPromotionBoundary :
      List SigmaDASHINativeProjectionBoundary

    nonPromotionBoundaryIsCanonical :
      nonPromotionBoundary
      ≡
      canonicalSigmaDASHINativeProjectionBoundaries

    futureAcceptedProjectionReceiptBlocked :
      SigmaDASHIAcceptedProjectionReceipt →
      ⊥

canonicalHEPDataT43DASHINativeProjectionReceiptRequestSurface :
  HEPDataT43DASHINativeProjectionReceiptRequestSurface
canonicalHEPDataT43DASHINativeProjectionReceiptRequestSurface =
  record
    { status =
        requestOnlyAwaitingDashiDynamicsBackedSigmaConstruction
    ; constructionRequirements =
        canonicalSigmaDASHIConstructionRequirements
    ; constructionRequirementsAreCanonical =
        refl
    ; dashiDynamicsBackedRoute =
        λ _ → requiresDashiDynamicsBackedSigmaSource
    ; dashiDynamicsBackedRouteIsSigmaSource =
        λ _ → refl
    ; fascisticContractionRoute =
        λ _ _ → requiresFascisticContractionRouteBinding
    ; fascisticContractionRouteIsBinding =
        λ _ _ → refl
    ; finiteTritEnumeration =
        canonicalSigmaDASHITritEnumeration
    ; finiteTritEnumerationIsCanonical =
        refl
    ; massDepthMap =
        t43SigmaDASHIMassDepth
    ; massDepthMapIsCanonical =
        λ _ → refl
    ; massRoleMap =
        t43SigmaDASHIMassRole
    ; massRoleMapIsCanonical =
        λ _ → refl
    ; phiStarBinShape =
        canonicalT43PhiStarBinShape
    ; phiStarProjectionLaw =
        λ _ _ → requiresPhiStarProjectionLaw
    ; phiStarProjectionLawIsRequired =
        λ _ _ → refl
    ; lambdaPolicy =
        canonicalSigmaDASHILambdaPolicy
    ; lambdaPolicyIsCanonical =
        refl
    ; observedT43RatiosMaySeedSigmaDASHI =
        false
    ; observedT43RatiosMaySeedSigmaDASHIIsFalse =
        refl
    ; projectionReceiptConstructedHere =
        false
    ; projectionReceiptConstructedHereIsFalse =
        refl
    ; comparisonLawReceiptConstructedHere =
        false
    ; comparisonLawReceiptConstructedHereIsFalse =
        refl
    ; w3PromotionConstructedHere =
        false
    ; w3PromotionConstructedHereIsFalse =
        refl
    ; w4PromotionConstructedHere =
        false
    ; w4PromotionConstructedHereIsFalse =
        refl
    ; w5PromotionConstructedHere =
        false
    ; w5PromotionConstructedHereIsFalse =
        refl
    ; w8PromotionConstructedHere =
        false
    ; w8PromotionConstructedHereIsFalse =
        refl
    ; requestedConstructionRoute =
        "Construct sigma_DASHI from a DashiDynamics Nat package; do not substitute the CSS/Sudakov baseline"
        ∷ "Bind the future sigma_DASHI source to the finite Trit enumeration [neg, zer, pos]"
        ∷ "Use the mass-depth map 50 <= M < 76 -> depth 2 and 76 <= M < 106 -> depth 2"
        ∷ "Project each t43 phi-star bin by the same law for both mass windows before taking the ratio"
        ∷ "Required ratio shape: sigma_DASHI(50 <= M < 76, bin) / sigma_DASHI(76 <= M < 106, bin)"
        ∷ "Fix lambda policy before projection and before comparison-law intake"
        ∷ []
    ; providerRequestFields =
        "dashiDynamicsPackage : DD.DashiDynamics Nat"
        ∷ "fascisticContractionRoute : finite-depth contraction binding, if the provider uses that route"
        ∷ "tritEnumeration : exact finite support [neg, zer, pos]"
        ∷ "massDepthMap : exact numerator/denominator mass-window depth map"
        ∷ "phiStarProjectionLaw : bin -> mass window -> sigma_DASHI projection law"
        ∷ "lambdaPolicy : fixed non-observed-ratio policy for projection"
        ∷ "cleanFreezeIdentity : future digest-bound identity, not constructed here"
        ∷ "projectionCompleteArtifact : future artifact, not constructed here"
        ∷ []
    ; nonPromotionBoundary =
        canonicalSigmaDASHINativeProjectionBoundaries
    ; nonPromotionBoundaryIsCanonical =
        refl
    ; futureAcceptedProjectionReceiptBlocked =
        sigmaDASHIAcceptedProjectionReceiptImpossibleHere
    }

canonicalNonPromotingHEPDataT43DASHINativeProjectionReceipt :
  HEPDataT43DASHINativeProjectionReceiptRequestSurface
canonicalNonPromotingHEPDataT43DASHINativeProjectionReceipt =
  canonicalHEPDataT43DASHINativeProjectionReceiptRequestSurface

canonicalHEPDataT43DASHINativeProjectionStatus :
  HEPDataT43DASHINativeProjectionStatus
canonicalHEPDataT43DASHINativeProjectionStatus =
  HEPDataT43DASHINativeProjectionReceiptRequestSurface.status
    canonicalHEPDataT43DASHINativeProjectionReceiptRequestSurface
