module DASHI.Core.ApplicationDependencyClassificationExact where

open import DASHI.Core.Prelude
open import DASHI.Core.TemporalSemanticGraphExact

------------------------------------------------------------------------
-- CONSERVATIVE BODY-REFERENCE CLASSIFICATION
--
-- A bare function-valued reference is not automatically a call.  Calls require
-- structural prefix-application evidence. Constructors used in a body are
-- construction evidence; local binder uses are value-flow evidence.
------------------------------------------------------------------------

data ReferenceContext : Set where
  typeReference : ReferenceContext
  bodyReference : ReferenceContext

data ReferenceTargetKind : Set where
  localBinderTarget : ReferenceTargetKind
  constructorTarget : ReferenceTargetKind
  callableTarget : ReferenceTargetKind
  otherTarget : ReferenceTargetKind

data ApplicationEvidence : Set where
  noApplicationEvidence : ApplicationEvidence
  prefixApplicationEvidence : ApplicationEvidence

classifyReference :
  ReferenceContext →
  ReferenceTargetKind →
  ApplicationEvidence →
  EdgeKind
classifyReference typeReference _ _ = typeDependsEdge
classifyReference bodyReference localBinderTarget _ = valueFlowsEdge
classifyReference bodyReference constructorTarget _ = constructsEdge
classifyReference bodyReference callableTarget prefixApplicationEvidence =
  callsEdge
classifyReference bodyReference callableTarget noApplicationEvidence =
  bodyDependsEdge
classifyReference bodyReference otherTarget _ = bodyDependsEdge

bareCallableReferenceIsNotCall :
  classifyReference
    bodyReference
    callableTarget
    noApplicationEvidence
  ≡ bodyDependsEdge
bareCallableReferenceIsNotCall = refl

prefixCallableReferenceIsCall :
  classifyReference
    bodyReference
    callableTarget
    prefixApplicationEvidence
  ≡ callsEdge
prefixCallableReferenceIsCall = refl

constructorBodyReferenceConstructs :
  ∀ evidence →
  classifyReference
    bodyReference
    constructorTarget
    evidence
  ≡ constructsEdge
constructorBodyReferenceConstructs _ = refl

localBodyReferenceFlows :
  ∀ evidence →
  classifyReference
    bodyReference
    localBinderTarget
    evidence
  ≡ valueFlowsEdge
localBodyReferenceFlows _ = refl

record ApplicationDependencyBoundary : Set where
  constructor applicationDependencyBoundary
  field
    bareCallableMayBePromotedWithoutEvidence : Bool
    bareCallableMayBePromotedWithoutEvidenceIsFalse :
      bareCallableMayBePromotedWithoutEvidence ≡ false

    mixfixSyntaxMayBeGuessedAsPrefixCall : Bool
    mixfixSyntaxMayBeGuessedAsPrefixCallIsFalse :
      mixfixSyntaxMayBeGuessedAsPrefixCall ≡ false

    theoremKindMayBeInferredFromFunctionSyntaxAlone : Bool
    theoremKindMayBeInferredFromFunctionSyntaxAloneIsFalse :
      theoremKindMayBeInferredFromFunctionSyntaxAlone ≡ false

canonicalApplicationDependencyBoundary :
  ApplicationDependencyBoundary
canonicalApplicationDependencyBoundary =
  applicationDependencyBoundary
    false refl
    false refl
    false refl


------------------------------------------------------------------------
-- ARGUMENT-FLOW ADMISSION
------------------------------------------------------------------------

data ApplicationPosition : Set where
  applicationHeadPosition : ApplicationPosition
  applicationArgumentPosition : ApplicationPosition
  standalonePosition : ApplicationPosition

argumentRelation :
  ApplicationPosition →
  EdgeKind
argumentRelation applicationHeadPosition = bodyDependsEdge
argumentRelation applicationArgumentPosition = argumentToEdge
argumentRelation standalonePosition = bodyDependsEdge

argumentPositionAdmitsArgumentEdge :
  argumentRelation applicationArgumentPosition
    ≡ argumentToEdge
argumentPositionAdmitsArgumentEdge = refl

standaloneReferenceIsNotArgumentFlow :
  argumentRelation standalonePosition
    ≡ bodyDependsEdge
standaloneReferenceIsNotArgumentFlow = refl
