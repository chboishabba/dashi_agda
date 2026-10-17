module DASHI.Reasoning.MonsterAlbertF4RelationProtocolBridgeExact where

------------------------------------------------------------------------
-- Compile the Monster-vs-classical-F4 discriminator into the repository's
-- existing relation-representation experiment protocol.
--
-- Attribution / authority discipline:
-- * sibling #1179 owns its proof-relevant finite 54->53 carrier/deletion weld
--   and a CONDITIONAL transported-Monster-action compiler;
-- * current master does not inhabit the actual Monster 54/53 action-recognition
--   input to that compiler;
-- * classical Albert/F4 sources retain historical/scientific attribution;
-- * DASHI owns the finite diagonal state realization, protocol composition and
--   non-promotion boundaries;
-- * no sibling theorem authority is imported here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Cognition.Teleodynamics.MonsterAlbertF4ActionDiscriminationHandoffExact as Handoff
import DASHI.Reasoning.RelationRepresentationAdequacyExact as Adequacy
import DASHI.Reasoning.RelationRepresentationExperimentProtocolExact as Protocol

strictMonsterAlbertF4Holdout : Protocol.HeldOutScope
strictMonsterAlbertF4Holdout =
  Protocol.heldOutScope true true true true
    "Hold out Monster/F4 actors or compositions, carrier states, model/checkpoint families and temporal interventions. Fit and held-out action words must be disjoint."

monsterAlbertF4RelationProtocol : Protocol.RelationExperimentProtocol
monsterAlbertF4RelationProtocol =
  Protocol.relationExperimentProtocol
    true
    "First acquire/inhabit the actual Monster 54/53 action recognition consumed by the already-paid #1179 transport compiler. Then compare that transported action against an independently supplied classical-F4 action on the same finite carrier. State embedding into literal rational-Albert copies is paid; the remaining algebraic bridge is a sheet-aware rational-linear action lift preserving the cubic norm and ACTUAL Albert unit."
    Protocol.contextualCandidate
    Adequacy.applicationSuppliedGeometry
    strictMonsterAlbertF4Holdout
    ("actual Monster 54/53 same-object action-recognition receipt" ∷
     "application of the paid transport compiler" ∷
     "held-out 54 action mismatch" ∷
     "held-out residual-53 action mismatch" ∷
     "removed distinguished-point compatibility" ∷
     "residual restriction compatibility" ∷
     "sheet action / sheet-preservation or explicit sheet-permutation receipt" ∷
     "rational-linear Albert action lift" ∷
     "cubic-norm compatibility of the lifted action" ∷
     "actual Albert-unit fixation of the lifted action" ∷
     "Jordan compatibility, measured directly or compiled by norm+unit rigidity" ∷
     "decoder compatibility" ∷
     "future consumer behaviour" ∷
     "target realization" ∷ [])
    true
    true
    false
    "The carrier/deletion weld and transport compiler are paid, but an actual Monster action instance is not. The finite state embedding is paid and preserves the transported finite product/cubic on its diagonal image; its named shape ScalarLine maps to Albert zero, not the unit. Native norm+unit rigidity becomes reusable only after a same-object rational-linear action lift preserving the cubic norm and actual unit. Successful fit remains consumer- and realization-relative and creates neither Monster ontology nor physical/phenomenal mechanism."

monsterAlbertF4ProtocolCandidateIsContextual :
  Protocol.candidate monsterAlbertF4RelationProtocol ≡ Protocol.contextualCandidate
monsterAlbertF4ProtocolCandidateIsContextual = refl

monsterAlbertF4ProtocolGeometryIsApplicationSupplied :
  Protocol.geometry monsterAlbertF4RelationProtocol ≡ Adequacy.applicationSuppliedGeometry
monsterAlbertF4ProtocolGeometryIsApplicationSupplied = refl

monsterAlbertF4ProtocolRequiresDynamicTrace :
  Protocol.dynamicTraceRequired monsterAlbertF4RelationProtocol ≡ true
monsterAlbertF4ProtocolRequiresDynamicTrace = refl

monsterAlbertF4ProtocolRequiresTargetRealization :
  Protocol.targetRealizationRequired monsterAlbertF4RelationProtocol ≡ true
monsterAlbertF4ProtocolRequiresTargetRealization = refl

monsterAlbertF4ProtocolDoesNotAutoGrantAuthority :
  Protocol.normativeAuthorityAutoGranted monsterAlbertF4RelationProtocol ≡ false
monsterAlbertF4ProtocolDoesNotAutoGrantAuthority = refl

record MonsterAlbertF4ProtocolBoundary : Set where
  constructor monster-albert-f4-protocol-boundary
  field
    existingRelationProtocolReused : Bool
    sameCarrierReceiptReused : Bool
    transportCompilerReceiptReused : Bool
    actualMonsterActionStillRequired : Bool
    allFourHoldoutAxesRequired : Bool
    heldOut54And53ActionRequired : Bool
    removedInvariantAndResidualRestrictionRequired : Bool
    finiteStateEmbeddingAlreadyPaid : Bool
    finiteActionLiftStillRequired : Bool
    sheetActionReceiptRequired : Bool
    cubicCompatibilityStillRequired : Bool
    actualUnitCompatibilityStillRequired : Bool
    removedPointCannotSubstituteForUnit : Bool
    cubicUnitRigidityOnlyAfterLinearActionLift : Bool
    decoderAndFutureConsumerRequired : Bool
    targetRealizationRequired : Bool
    actionFitCreatesClassicalF4Recognition : Bool
    actionFitCreatesMechanismIdentity : Bool
open MonsterAlbertF4ProtocolBoundary public

canonicalMonsterAlbertF4ProtocolBoundary : MonsterAlbertF4ProtocolBoundary
canonicalMonsterAlbertF4ProtocolBoundary =
  monster-albert-f4-protocol-boundary
    true
    (Handoff.proofRelevantCarrierIdentityPaidInSibling Handoff.canonicalMonsterAlbertF4ActionBoundary)
    (Handoff.transportCompilerPaidInSibling Handoff.canonicalMonsterAlbertF4ActionBoundary)
    true
    true
    true
    true
    (Handoff.finiteStateEmbeddingToLinearAlbertPaid Handoff.canonicalMonsterAlbertF4ActionBoundary)
    (Handoff.finiteActionLiftToLinearAlbertRequired Handoff.canonicalMonsterAlbertF4ActionBoundary)
    true
    true
    true
    true
    (Handoff.cubicUnitRigidityReusableAfterLinearActionLift Handoff.canonicalMonsterAlbertF4ActionBoundary)
    true
    true
    false
    false
