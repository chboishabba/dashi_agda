module DASHI.Reasoning.MonsterAlbertF4RelationProtocolBridgeExact where

------------------------------------------------------------------------
-- Compile the Monster-transported-vs-classical-F4 action discriminator into
-- the repository's existing relation-representation experiment protocol.
--
-- Attribution / authority discipline:
-- * sibling #1179 owns its proof-relevant finite 54->53 carrier/deletion weld
--   and conditional transported-Monster-action compiler;
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
    "Compare the independently supplied classical-F4 action against the transported Monster action on the same finite 54->53 carrier. State-level embedding into literal rational-Albert copies is already paid. The live bridge is sheet-aware rational-linear action lifting, cubic-norm preservation and fixation of the ACTUAL Albert unit; the removed finite-shape point maps to Albert zero and cannot substitute for the unit."
    Protocol.contextualCandidate
    Adequacy.applicationSuppliedGeometry
    strictMonsterAlbertF4Holdout
    ("held-out 54 action mismatch" ∷
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
    "The finite state embedding is already paid and preserves the transported finite product/cubic on its diagonal image. However, its named shape ScalarLine maps to Albert zero, not the unit. Extensional finite-action agreement is therefore below classical F4 recognition. Native norm+unit rigidity is reusable only after a same-object rational-linear action lift preserving the cubic norm and actual unit. Successful held-out fit remains consumer- and realization-relative and creates neither Monster ontology nor physical/phenomenal mechanism."

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
    transportedMonsterActionReceiptReused : Bool
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
    (Handoff.transportedMonsterActionPaidInSibling Handoff.canonicalMonsterAlbertF4ActionBoundary)
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
