module DASHI.Physics.YangMills.BalabanSpatialLinkWeightLowerBound where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support

Scalar : Set
Scalar = String

data SpatialLinkWeightSource : Set where
  unitSpatialCost : SpatialLinkWeightSource
  anisotropicAxisCost : SpatialLinkWeightSource
  fieldRegularityCost : SpatialLinkWeightSource
  treeDistanceDecayRateCost : SpatialLinkWeightSource
  unassignedCost : SpatialLinkWeightSource

record SpatialSupportLinkWeightInterface : Set where
  field
    linkWeight :
      Support.Link → Scalar
    spatialSupportLinkWeight :
      (e : Support.Link) →
      Support.SpatialLink e →
      Scalar
    declaredMinLinkWeight :
      Scalar
    positiveLowerBoundWitnessAvailable :
      Bool
    kpSafeLowerBoundWitnessAvailable :
      Bool
    positiveLowerBoundWitnessAvailableIsFalse :
      positiveLowerBoundWitnessAvailable ≡ false
    kpSafeLowerBoundWitnessAvailableIsFalse :
      kpSafeLowerBoundWitnessAvailable ≡ false
    weakTarget :
      String
    weakTargetIsCanonical :
      weakTarget ≡ "minLinkWeight > 0"
    strongTarget :
      String
    strongTargetIsCanonical :
      strongTarget ≡ "minLinkWeight > 0.9271"
    interfaceBoundary :
      String
    interfaceBoundaryIsCanonical :
      interfaceBoundary ≡
      "The YM lane still lacks a typed spatial support-link weight definition with quantitative lower-bound witness; this interface only names the function that the next worker must fill."
    noClayPromotion :
      clayYangMillsPromoted ≡ false

currentSpatialSupportLinkWeightInterface :
  SpatialSupportLinkWeightInterface
currentSpatialSupportLinkWeightInterface = record
  { linkWeight = λ _ → "unassigned"
  ; spatialSupportLinkWeight = λ _ _ → "unassigned"
  ; declaredMinLinkWeight = "0.0"
  ; positiveLowerBoundWitnessAvailable = false
  ; kpSafeLowerBoundWitnessAvailable = false
  ; positiveLowerBoundWitnessAvailableIsFalse = refl
  ; kpSafeLowerBoundWitnessAvailableIsFalse = refl
  ; weakTarget = "minLinkWeight > 0"
  ; weakTargetIsCanonical = refl
  ; strongTarget = "minLinkWeight > 0.9271"
  ; strongTargetIsCanonical = refl
  ; interfaceBoundary =
      "The YM lane still lacks a typed spatial support-link weight definition with quantitative lower-bound witness; this interface only names the function that the next worker must fill."
  ; interfaceBoundaryIsCanonical = refl
  ; noClayPromotion = refl
  }

record SpatialSupportLinkWeightDefinition : Set where
  field
    source : SpatialLinkWeightSource
    interface : SpatialSupportLinkWeightInterface
    linkWeightDefined : Bool
    unitNormalised : Bool
    lowerBoundWeak : Bool
    lowerBoundKPSafe : Bool
    linkWeightDefinedIsFalse :
      linkWeightDefined ≡ false
    unitNormalisedIsFalse :
      unitNormalised ≡ false
    lowerBoundWeakIsFalse :
      lowerBoundWeak ≡ false
    lowerBoundKPSafeIsFalse :
      lowerBoundKPSafe ≡ false
    sourceSearchStatus : String
    sourceSearchStatusIsCanonical :
      sourceSearchStatus ≡
      "Source check: Balaban/Dimock bounds expose exponential decay exp (-kappa * d_k(X)), but the repo does not yet identify that tree-distance decay rate with a concrete spatial support-link weight in the active DASHI diameter interface."
    sourceCandidateSummary : String
    sourceCandidateSummaryIsCanonical :
      sourceCandidateSummary ≡
      "Best current candidate source is treeDistanceDecayRateCost: one unit of tree distance carries decay rate kappa > 0, but kappa = 1 and diameter-unit compatibility are not yet promoted here."
    noClayPromotion :
      clayYangMillsPromoted ≡ false

currentSpatialSupportLinkWeightDefinition :
  SpatialSupportLinkWeightDefinition
currentSpatialSupportLinkWeightDefinition = record
  { source = unassignedCost
  ; interface = currentSpatialSupportLinkWeightInterface
  ; linkWeightDefined = false
  ; unitNormalised = false
  ; lowerBoundWeak = false
  ; lowerBoundKPSafe = false
  ; linkWeightDefinedIsFalse = refl
  ; unitNormalisedIsFalse = refl
  ; lowerBoundWeakIsFalse = refl
  ; lowerBoundKPSafeIsFalse = refl
  ; sourceSearchStatus =
      "Source check: Balaban/Dimock bounds expose exponential decay exp (-kappa * d_k(X)), but the repo does not yet identify that tree-distance decay rate with a concrete spatial support-link weight in the active DASHI diameter interface."
  ; sourceSearchStatusIsCanonical = refl
  ; sourceCandidateSummary =
      "Best current candidate source is treeDistanceDecayRateCost: one unit of tree distance carries decay rate kappa > 0, but kappa = 1 and diameter-unit compatibility are not yet promoted here."
  ; sourceCandidateSummaryIsCanonical = refl
  ; noClayPromotion = refl
  }

record SpatialLinkWeightLowerBound : Set where
  field
    weightDefinition : SpatialSupportLinkWeightDefinition
    weightInterface : SpatialSupportLinkWeightInterface
    minLinkWeight : Scalar
    positiveLowerBoundAvailable : Bool
    kpMarginLowerBoundAvailable : Bool
    singleLinkBaseAvailable : Bool
    positiveLowerBoundAvailableIsFalse :
      positiveLowerBoundAvailable ≡ false
    kpMarginLowerBoundAvailableIsFalse :
      kpMarginLowerBoundAvailable ≡ false
    singleLinkBaseAvailableIsFalse :
      singleLinkBaseAvailable ≡ false
    targetWeakLowerBound : String
    targetWeakLowerBoundIsCanonical :
      targetWeakLowerBound ≡ "minLinkWeight > 0"
    weakDerivationRoute : String
    weakDerivationRouteIsCanonical :
      weakDerivationRoute ≡
      "field regularity -> every admissible spatial support link has positive anisotropic weight -> minLinkWeight > 0"
    targetStrongLowerBound : String
    targetStrongLowerBoundIsCanonical :
      targetStrongLowerBound ≡ "minLinkWeight > 0.9271"
    definitionSearchStatus : String
    definitionSearchStatusIsCanonical :
      definitionSearchStatus ≡
      "No concrete spatial anisotropic link-weight definition has been located in the current YM lane."
    nearbyStubSurface : String
    nearbyStubSurfaceIsCanonical :
      nearbyStubSurface ≡
      "BalabanPolymerDiameterEntropy only exposes the placeholder weight = λ _ -> candidate, so no typed link-weight lower bound can be derived there."
    exactMissingHypothesis : String
    exactMissingHypothesisIsCanonical :
      exactMissingHypothesis ≡
      "Spatial support link weights must be normalised so that minLinkWeight > 0.9271."
    currentBlocker : String
    currentBlockerIsCanonical :
      currentBlocker ≡
      "No typed spatial link-weight lower-bound witness has been located yet: the weak base case needs field regularity -> every admissible spatial support link has positive anisotropic weight -> minLinkWeight > 0, and the KP margin needs the stronger normalisation minLinkWeight > 0.9271."
    noClayPromotion : clayYangMillsPromoted ≡ false

currentSpatialLinkWeightLowerBound :
  SpatialLinkWeightLowerBound
currentSpatialLinkWeightLowerBound = record
  { weightDefinition = currentSpatialSupportLinkWeightDefinition
  ; weightInterface = currentSpatialSupportLinkWeightInterface
  ; minLinkWeight = "0.0"
  ; positiveLowerBoundAvailable = false
  ; kpMarginLowerBoundAvailable = false
  ; singleLinkBaseAvailable = false
  ; positiveLowerBoundAvailableIsFalse = refl
  ; kpMarginLowerBoundAvailableIsFalse = refl
  ; singleLinkBaseAvailableIsFalse = refl
  ; targetWeakLowerBound = "minLinkWeight > 0"
  ; targetWeakLowerBoundIsCanonical = refl
  ; weakDerivationRoute =
      "field regularity -> every admissible spatial support link has positive anisotropic weight -> minLinkWeight > 0"
  ; weakDerivationRouteIsCanonical = refl
  ; targetStrongLowerBound = "minLinkWeight > 0.9271"
  ; targetStrongLowerBoundIsCanonical = refl
  ; definitionSearchStatus =
      "No concrete spatial anisotropic link-weight definition has been located in the current YM lane."
  ; definitionSearchStatusIsCanonical = refl
  ; nearbyStubSurface =
      "BalabanPolymerDiameterEntropy only exposes the placeholder weight = λ _ -> candidate, so no typed link-weight lower bound can be derived there."
  ; nearbyStubSurfaceIsCanonical = refl
  ; exactMissingHypothesis =
      "Spatial support link weights must be normalised so that minLinkWeight > 0.9271."
  ; exactMissingHypothesisIsCanonical = refl
  ; currentBlocker =
      "No typed spatial link-weight lower-bound witness has been located yet: the weak base case needs field regularity -> every admissible spatial support link has positive anisotropic weight -> minLinkWeight > 0, and the KP margin needs the stronger normalisation minLinkWeight > 0.9271."
  ; currentBlockerIsCanonical = refl
  ; noClayPromotion = refl
  }

record SpatialLinkRegularityAssumption : Set where
  field
    fieldRegularityAvailable : Bool
    linkWeightFunctionAvailable : Bool
    linkWeightLowerBound : Scalar
    everyAdmissibleSpatialSupportLinkHasPositiveWeight : Bool
    linkWeightLowerBoundPositive : Bool
    linkWeightBeatsKPMargin : Bool
    spatialSupportLinkWeightsNormalisedForKPMargin : Bool
    fieldRegularityAvailableIsFalse :
      fieldRegularityAvailable ≡ false
    linkWeightFunctionAvailableIsFalse :
      linkWeightFunctionAvailable ≡ false
    everyAdmissibleSpatialSupportLinkHasPositiveWeightIsFalse :
      everyAdmissibleSpatialSupportLinkHasPositiveWeight ≡ false
    linkWeightLowerBoundPositiveIsFalse :
      linkWeightLowerBoundPositive ≡ false
    linkWeightBeatsKPMarginIsFalse :
      linkWeightBeatsKPMargin ≡ false
    spatialSupportLinkWeightsNormalisedForKPMarginIsFalse :
      spatialSupportLinkWeightsNormalisedForKPMargin ≡ false
    weakPositivityRoute : String
    weakPositivityRouteIsCanonical :
      weakPositivityRoute ≡
      "field regularity -> every admissible spatial support link has positive anisotropic weight -> minLinkWeight > 0"
    strongNormalisationRequirement : String
    strongNormalisationRequirementIsCanonical :
      strongNormalisationRequirement ≡
      "spatial support link weights must be normalised so that minLinkWeight > 0.9271"
    searchedDefinitionStatus : String
    searchedDefinitionStatusIsCanonical :
      searchedDefinitionStatus ≡
      "Search result: no typed spatial anisotropic support-link weight function is currently exposed by the YM support and compatibility modules."
    nearestWeightSurface : String
    nearestWeightSurfaceIsCanonical :
      nearestWeightSurface ≡
      "Nearest weight surface found: BalabanPolymerDiameterEntropy uses only the stub weight = λ _ -> candidate."
    missingInputSummary : String
    missingInputSummaryIsCanonical :
      missingInputSummary ≡
      "Missing first mathematical input: a typed spatial link-weight lower bound, with weak route via field regularity and strong requirement that spatial support link weights be normalised so that minLinkWeight > 0.9271."
    noClayPromotion : clayYangMillsPromoted ≡ false

currentSpatialLinkRegularityAssumption :
  SpatialLinkRegularityAssumption
currentSpatialLinkRegularityAssumption = record
  { fieldRegularityAvailable = false
  ; linkWeightFunctionAvailable = false
  ; linkWeightLowerBound = "0.0"
  ; everyAdmissibleSpatialSupportLinkHasPositiveWeight = false
  ; linkWeightLowerBoundPositive = false
  ; linkWeightBeatsKPMargin = false
  ; spatialSupportLinkWeightsNormalisedForKPMargin = false
  ; fieldRegularityAvailableIsFalse = refl
  ; linkWeightFunctionAvailableIsFalse = refl
  ; everyAdmissibleSpatialSupportLinkHasPositiveWeightIsFalse = refl
  ; linkWeightLowerBoundPositiveIsFalse = refl
  ; linkWeightBeatsKPMarginIsFalse = refl
  ; spatialSupportLinkWeightsNormalisedForKPMarginIsFalse = refl
  ; weakPositivityRoute =
      "field regularity -> every admissible spatial support link has positive anisotropic weight -> minLinkWeight > 0"
  ; weakPositivityRouteIsCanonical = refl
  ; strongNormalisationRequirement =
      "spatial support link weights must be normalised so that minLinkWeight > 0.9271"
  ; strongNormalisationRequirementIsCanonical = refl
  ; searchedDefinitionStatus =
      "Search result: no typed spatial anisotropic support-link weight function is currently exposed by the YM support and compatibility modules."
  ; searchedDefinitionStatusIsCanonical = refl
  ; nearestWeightSurface =
      "Nearest weight surface found: BalabanPolymerDiameterEntropy uses only the stub weight = λ _ -> candidate."
  ; nearestWeightSurfaceIsCanonical = refl
  ; missingInputSummary =
      "Missing first mathematical input: a typed spatial link-weight lower bound, with weak route via field regularity and strong requirement that spatial support link weights be normalised so that minLinkWeight > 0.9271."
  ; missingInputSummaryIsCanonical = refl
  ; noClayPromotion = refl
  }
