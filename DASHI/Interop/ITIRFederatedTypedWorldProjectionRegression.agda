module DASHI.Interop.ITIRFederatedTypedWorldProjectionRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)

import DASHI.Interop.ITIRFederatedTypedWorldProjectionExact as W

------------------------------------------------------------------------
-- Regression surface: pin the ownership and non-promotion coordinates that
-- documentation now relies on.
------------------------------------------------------------------------

slrDoesNotOwnSecondWorld :
  W.slrBuildsSecondGlobalWorldModel ≡ false
slrDoesNotOwnSecondWorld = refl

digitalESDIsNotCoreOntology :
  W.digitalESDDefinesCoreEvidenceOntology ≡ false
digitalESDIsNotCoreOntology = refl

ribbonIsProjectionOnly :
  W.ribbonOwnsFinanceTruth ≡ false
ribbonIsProjectionOnly = refl

statiBakerIsTemporalNotSemanticAuthority :
  W.statiBakerOwnsSemanticWorldTruth ≡ false
statiBakerIsTemporalNotSemanticAuthority = refl

projectionPreservesIdentity :
  (node : W.SourceAddressableSemanticNode) →
  W.semanticIdentity
    (W.sameSemanticTarget node W.ribbonSankeyProjection)
  ≡ W.semanticIdentity node
projectionPreservesIdentity node =
  W.projectionIdentityPreserved node W.ribbonSankeyProjection

missingObservationDoesNotMeanAbsence :
  W.MissingObservationCreatesObservedAbsence → ⊥
missingObservationDoesNotMeanAbsence =
  W.missingObservationIsNotObservedAbsence

crossStreamAlignmentDoesNotMeanCausation :
  W.CrossStreamAlignmentCreatesCausation → ⊥
crossStreamAlignmentDoesNotMeanCausation =
  W.crossStreamAlignmentIsNotCausation

formalProofDoesNotCreateWorldTruth :
  W.FormalProofCreatesExternalWorldTruth → ⊥
formalProofDoesNotCreateWorldTruth =
  W.formalProofIsNotExternalWorldTruth

typedRefinementDoesNotForkEvidenceOntology :
  W.TypedRefinementCreatesNewCanonicalEvidenceUniverse → ⊥
typedRefinementDoesNotForkEvidenceOntology =
  W.typedRefinementIsNotNewCanonicalEvidenceUniverse

caseySelectionDoesNotCreateWorldTruth :
  W.CaseySelectionCreatesWorldTruth → ⊥
caseySelectionDoesNotCreateWorldTruth =
  W.caseySelectionIsNotWorldTruth

projectionDoesNotCreateCanonicalState :
  W.ProjectionCreatesCanonicalState → ⊥
projectionDoesNotCreateCanonicalState =
  W.projectionIsNotCanonicalState
