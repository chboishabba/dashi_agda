module DASHI.Geometry.SeaMeInItAuthorityInvariants where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Governance.GovernedArtifactCore
open import DASHI.Geometry.SeaMeInItGovernedPipeline

------------------------------------------------------------------------
-- Hash selection is decision-indexed as well as source-indexed.

selectedHashFor : Decision → Hash → Hash → Hash
selectedHashFor promote rawHash refinedHash = refinedHash
selectedHashFor abstain rawHash refinedHash = rawHash
selectedHashFor reject  rawHash refinedHash = rawHash

record BodyCarrierLineageInvariant (carrier : BodyCarrierReceiptV2) : Set where
  constructor bodyCarrierLineageInvariant
  field
    selectedHashMatchesDecision :
      selectedPreRepairHash carrier ≡
      selectedHashFor
        (refinementDecision carrier)
        (rawReprojectionHash carrier)
        (refinedPreRepairHash carrier)

open BodyCarrierLineageInvariant public

------------------------------------------------------------------------
-- Promotion of a body carrier requires evidence about the final export, not
-- only the pre-repair checkpoint.


data FinalArtifactAuthorization
  (evidence : FinalExportEvidence) : Decision → Set where
  authorizeFinal :
    finiteCoordinates (topology evidence) ≡ true →
    legalFaceIndices (topology evidence) ≡ true →
    closedEdges (topology evidence) ≡ true →
    connectedSurface (topology evidence) ≡ true →
    FinalArtifactAuthorization evidence promote
  abstainFinal : FinalArtifactAuthorization evidence abstain
  rejectFinal  : FinalArtifactAuthorization evidence reject

record AuthorizedBodyCarrier (carrier : BodyCarrierReceiptV2) : Set where
  constructor authorizedBodyCarrier
  field
    lineageInvariant : BodyCarrierLineageInvariant carrier
    finalAuthorization :
      FinalArtifactAuthorization
        (finalExportEvidence carrier)
        (bodyDecision carrier)

open AuthorizedBodyCarrier public

------------------------------------------------------------------------
-- A promoted carrier may grant a named consumer authority.  There is no
-- constructor for abstaining or rejected carriers.


data CanConsumeBody
  (carrier : BodyCarrierReceiptV2)
  (consumer : Consumer) : Set where
  consumePromotedBody :
    bodyDecision carrier ≡ promote →
    CanConsumeBody carrier consumer

------------------------------------------------------------------------
-- Gate 6 transitions are admissible as materialized states only when geometry
-- and all state-dependent evidence were recomputed.

record MaterializedPanelTransition (transition : PanelTransition) : Set where
  constructor materializedPanelTransition
  field
    facesPreserved : faceConservation (recomputedEvidence transition) ≡ true
    topologyChecked : topologyValid (recomputedEvidence transition) ≡ true
    geometryChecked : geometryFinite (recomputedEvidence transition) ≡ true
    backendActuallyRerun : backendRerun (recomputedEvidence transition) ≡ true
    residualActuallyRecomputed :
      residualsRecomputed (recomputedEvidence transition) ≡ true
    operatorsActuallyRecomputed :
      admissibleOperatorsRecomputed (recomputedEvidence transition) ≡ true

open MaterializedPanelTransition public

record SequentialPairAuthority (pair : OrderedMaterializedPair) : Set where
  constructor sequentialPairAuthority
  field
    firstMaterialized : MaterializedPanelTransition (firstTransition pair)
    secondMaterialized : MaterializedPanelTransition (secondTransition pair)
    firstFlagTrue : firstActuallyMaterialized pair ≡ true
    secondFlagTrue : secondActuallyMaterialized pair ≡ true

open SequentialPairAuthority public

-- Beam admission remains logically distinct from production promotion.
record BeamAdmissionWithoutPromotion (transition : PanelTransition) : Set where
  constructor beamAdmissionWithoutPromotion
  field
    admitted : searchDecision transition ≡ admitToBeam
    notYetProductionAuthority : productionDecision transition ≡ abstain

open BeamAdmissionWithoutPromotion public

------------------------------------------------------------------------
-- BT369 is warranted only for the serialization-specific diagnosis.

record BT369Warrant (indication : BT369SerializerIndication) : Set where
  constructor bt369Warrant
  field
    validGeometry : validGarmentGeometryExists indication ≡ true
    serializationFailure : currentSerializationFails indication ≡ true
    basisAdequate : operatorBasisAdequate indication ≡ true
    panelsAdequate : panelizationAdequate indication ≡ true
    physicsFeasible : physicalPolicyFeasible indication ≡ true

open BT369Warrant public

-- A failed bounded search alone is intentionally insufficient.
boundedSearchFailureAloneWarrantsBT369 : Bool
boundedSearchFailureAloneWarrantsBT369 = false
