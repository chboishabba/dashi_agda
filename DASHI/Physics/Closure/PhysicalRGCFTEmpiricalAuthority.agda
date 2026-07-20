module DASHI.Physics.Closure.PhysicalRGCFTEmpiricalAuthority where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List)

open import DASHI.Physics.Closure.PhysicalRealComplexRGCFTRoute as Route

------------------------------------------------------------------------
-- External authority required to promote a unified route from a theorem target
-- to a physical claim.
--
-- The previous reference models are useful witnesses of consistency and API
-- inhabitation, but they are not measurements.  This record therefore requires
-- provenance, uncertainty, independent authority, model comparison, and explicit
-- falsification criteria for every physical lane.

record PhysicalEvidenceProvenance : Set₁ where
  field
    sourceLabel : String
    sourceKind : String
    sourceRef : String
    datasetIdentifier : String
    analysisVersion : String
    extractionMethod : String
    note : String

open PhysicalEvidenceProvenance public

record PhysicalRGCFTValidationAuthority
  (R : Route.PhysicalFixedPointRGCFTRoute)
  : Setω where
  field
    provenance : List PhysicalEvidenceProvenance

    scalarCarrierIsPhysicalRealOrComplex : Set
    banachTangentIdentifiedWithDeclaredSystem : Set
    realTimeGeneratorValidated : Set
    semigroupEstimatesNumericallyOrAnalyticallyChecked : Set

    anomalousDimensionsMeasured : Set
    anomalousDimensionUncertaintiesAudited : Set
    renormalizationSchemeMatched : Set

    singularOPEComparedToCorrelationData : Set
    conformalBlockFitAccepted : Set
    crossingResidualWithinDeclaredTolerance : Set

    depthEnvelopeComparedToFiniteApproximants : Set
    rgIntertwinerCheckedAcrossMultipleDepths : Set
    universalityTestedAcrossRegulatorsOrSchemes : Set

    stressTensorCorrelationNontrivialAndMeasured : Set
    centralChargeMeasuredOrDerivedFromIndependentAuthority : Set
    wardResidualsWithinDeclaredTolerance : Set

    noCircularUseOfTargetClaim : Set
    independentReplicationOrPrimaryAuthority : Set
    competingModelComparison : Set
    falsificationCriteriaDeclared : Set

    validationSummary : String
    validationVersion : String

open PhysicalRGCFTValidationAuthority public

------------------------------------------------------------------------
-- Promotion is possible only when both the unified route and its authority are
-- supplied.  There is intentionally no canonical constructor invocation in this
-- module.

data PhysicalRGCFTPromotion : Setω where
  promotePhysicalRGCFT :
    (route : Route.PhysicalFixedPointRGCFTRoute) →
    PhysicalRGCFTValidationAuthority route →
    PhysicalRGCFTPromotion

record PhysicalRGCFTCompletionReceipt : Setω where
  field
    route : Route.PhysicalFixedPointRGCFTRoute
    authority : PhysicalRGCFTValidationAuthority route
    promotion : PhysicalRGCFTPromotion
    promotionMatchesRoute : Set
    declaredEvidenceCount : Nat
    receiptLabel : String

open PhysicalRGCFTCompletionReceipt public
