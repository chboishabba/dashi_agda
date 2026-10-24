module DASHI.Reasoning.LilaExceptionalWeylRelationProtocolBridgeExact where

------------------------------------------------------------------------
-- Compile the exceptional-Weyl / Tits experiment into the repository's
-- pre-existing relation-representation experiment protocol rather than owning
-- a second experiment calculus.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Reasoning.RelationRepresentationAdequacyExact as Adequacy
import DASHI.Reasoning.RelationRepresentationExperimentProtocolExact as Protocol
import DASHI.Reasoning.LilaExceptionalWeylExperimentMaxCutExact as Weyl

strictExceptionalWeylHoldout : Protocol.HeldOutScope
strictExceptionalWeylHoldout =
  Protocol.heldOutScope true true true true
    "Hold out semantic intervention targets, contexts/prompts, model families/seeds and temporal checkpoints. Weyl/Tits words used for fit are disjoint from held-out composition words."

exceptionalWeylRelationProtocol : Protocol.RelationExperimentProtocol
exceptionalWeylRelationProtocol =
  Protocol.relationExperimentProtocol
    true
    "Compare matched semantic interventions under a predeclared exceptional candidate action; root/weight codebook use alone is not a matched-action receipt."
    Protocol.contextualCandidate
    Adequacy.applicationSuppliedGeometry
    strictExceptionalWeylHoldout
    ("generator action fit" ∷
     "Coxeter/Tits composition residual" ∷
     "decoder compatibility" ∷
     "future consumer language" ∷
     "target realization" ∷ [])
    true
    true
    false
    "E6/F4/E8 candidate mathematics is supplied by existing Weyl/root owners. The experiment tests whether the actual model representation intertwines those actions on held-out interventions and words. Failure reopens candidate search; success remains consumer- and realization-relative."

exceptionalProtocolCandidateIsContextual :
  Protocol.candidate exceptionalWeylRelationProtocol ≡ Protocol.contextualCandidate
exceptionalProtocolCandidateIsContextual = refl

exceptionalProtocolGeometryIsApplicationSupplied :
  Protocol.geometry exceptionalWeylRelationProtocol ≡ Adequacy.applicationSuppliedGeometry
exceptionalProtocolGeometryIsApplicationSupplied = refl

exceptionalProtocolRequiresDynamicTrace :
  Protocol.dynamicTraceRequired exceptionalWeylRelationProtocol ≡ true
exceptionalProtocolRequiresDynamicTrace = refl

exceptionalProtocolRequiresTargetRealization :
  Protocol.targetRealizationRequired exceptionalWeylRelationProtocol ≡ true
exceptionalProtocolRequiresTargetRealization = refl

exceptionalProtocolDoesNotAutoGrantAuthority :
  Protocol.normativeAuthorityAutoGranted exceptionalWeylRelationProtocol ≡ false
exceptionalProtocolDoesNotAutoGrantAuthority = refl

record WeylProtocolReuseBoundary : Set where
  constructor weyl-protocol-reuse-boundary
  field
    existingRelationProtocolReused : Bool
    existingCandidateCollisionReopeningReused : Bool
    allFourHoldoutAxesRequired : Bool
    dynamicTraceRequired : Bool
    targetRealizationRequired : Bool
    normativeAuthorityAutoGranted : Bool
    mathematicalWeylReceiptCountsAsEmpiricalModelFit : Bool
open WeylProtocolReuseBoundary public

canonicalWeylProtocolReuseBoundary : WeylProtocolReuseBoundary
canonicalWeylProtocolReuseBoundary =
  weyl-protocol-reuse-boundary
    true true true true true false false
