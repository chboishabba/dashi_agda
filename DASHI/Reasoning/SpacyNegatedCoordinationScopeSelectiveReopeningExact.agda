module DASHI.Reasoning.SpacyNegatedCoordinationScopeSelectiveReopeningExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Reasoning.SpacyNegatedCoordinationScopeTraceExact as Trace
import DASHI.Reasoning.LogicalConsequenceDerivationPathExact as Path
import DASHI.Reasoning.DerivationEdgeInstanceSelectiveReopeningExact as Reopen

------------------------------------------------------------------------
-- MATERIALISED SPACY SCOPE HISTORY -> PATH-INSTANCE REOPENING
--
-- The concrete SensibLaw sentence in SpacyNegatedCoordinationScopeTraceExact
-- has two parser-supported scope histories.  They may reconverge on the same
-- reviewed final formula, but the derivation route is retained separately.
-- A later scope correction therefore reopens only a certificate whose exact
-- scope edge occurred in its indexed derivation path.
------------------------------------------------------------------------

broadScopeNode : Path.DerivationNode
broadScopeNode =
  Path.derivationNode
    "spacy-scope:broad"
    Trace.broadBody
    Trace.reviewedAssertion
    Path.parserCandidateAuthority
    "materialised spaCy neg edge + broad coordination-scope candidate"

narrowScopeNode : Path.DerivationNode
narrowScopeNode =
  Path.derivationNode
    "spacy-scope:narrow"
    Trace.narrowBody
    Trace.reviewedAssertion
    Path.parserCandidateAuthority
    "materialised spaCy neg edge + narrow coordination-scope candidate"

reviewedFinalNode : Path.DerivationNode
reviewedFinalNode =
  Path.derivationNode
    "spacy-scope:reviewed-final"
    Trace.finalFormula
    Trace.reviewedAssertion
    Path.reviewedSemanticAuthority
    "reviewed PNF normal form after scope adjudication"

broadScopeStep : Path.DerivationStep broadScopeNode reviewedFinalNode
broadScopeStep =
  Path.derivationStep
    Path.semanticResolutionEdge
    "scope-resolution:broad->reviewed-final"
    "semantic review receipt + 369 first-pass route"
    "broad scope route retained even after formula reconvergence"

narrowScopeStep : Path.DerivationStep narrowScopeNode reviewedFinalNode
narrowScopeStep =
  Path.derivationStep
    Path.semanticResolutionEdge
    "scope-resolution:narrow->reviewed-final"
    "semantic review receipt + 369 revised route"
    "narrow scope route retained even after formula reconvergence"

broadScopeEdge : Reopen.IndexedDerivationEdge broadScopeNode reviewedFinalNode
broadScopeEdge =
  Reopen.indexedDerivationEdge
    "edge:materialised-spacy-broad-scope"
    broadScopeStep
    "SpacyNegatedCoordinationScopeTraceExact.negBroadCandidate"
    "replay from materialised neg/conjunction dependency witnesses"

narrowScopeEdge : Reopen.IndexedDerivationEdge narrowScopeNode reviewedFinalNode
narrowScopeEdge =
  Reopen.indexedDerivationEdge
    "edge:materialised-spacy-narrow-scope"
    narrowScopeStep
    "SpacyNegatedCoordinationScopeTraceExact.negNarrowCandidate"
    "replay from the same parser evidence with narrow scope adjudication"

broadIndexedPath :
  Reopen.IndexedDerivationPath broadScopeNode reviewedFinalNode
broadIndexedPath =
  Reopen.indexedStep broadScopeEdge Reopen.indexedRefl

narrowIndexedPath :
  Reopen.IndexedDerivationPath narrowScopeNode reviewedFinalNode
narrowIndexedPath =
  Reopen.indexedStep narrowScopeEdge Reopen.indexedRefl

broadEdgeOccursInBroadPath :
  Reopen.EdgeOccurs broadScopeEdge broadIndexedPath
broadEdgeOccursInBroadPath = Reopen.occursHere

narrowEdgeOccursInNarrowPath :
  Reopen.EdgeOccurs narrowScopeEdge narrowIndexedPath
narrowEdgeOccursInNarrowPath = Reopen.occursHere

------------------------------------------------------------------------
-- Both routes end at exactly the same reviewed formula.
------------------------------------------------------------------------

broadFinalFormula : Path.formula reviewedFinalNode ≡ Trace.finalFormula
broadFinalFormula = refl

narrowFinalFormula : Path.formula reviewedFinalNode ≡ Trace.finalFormula
narrowFinalFormula = refl

sameFinalFormulaAcrossScopeHistories :
  Path.formula reviewedFinalNode ≡ Path.formula reviewedFinalNode
sameFinalFormulaAcrossScopeHistories = refl

------------------------------------------------------------------------
-- Each certificate owns the exact path it used.
------------------------------------------------------------------------

broadScopeCertificate : Reopen.IndexedConsequenceCertificate
broadScopeCertificate =
  Reopen.indexedConsequenceCertificate
    broadScopeNode
    reviewedFinalNode
    broadIndexedPath
    "certificate:materialised-spacy-broad-history"
    "same final formula, broad parser/semantic/369 history retained"
    "reviewed semantic authority"

narrowScopeCertificate : Reopen.IndexedConsequenceCertificate
narrowScopeCertificate =
  Reopen.indexedConsequenceCertificate
    narrowScopeNode
    reviewedFinalNode
    narrowIndexedPath
    "certificate:materialised-spacy-narrow-history"
    "same final formula, narrow parser/semantic/369 history retained"
    "reviewed semantic authority"

broadScopeRevisionReopensBroadCertificate :
  Dependency.ReopeningObligation
    (Reopen.OccurrenceDepends broadScopeEdge broadScopeCertificate)
    Reopen.changedEdgeInstanceArtifact
    Reopen.consequenceCertificateArtifact
broadScopeRevisionReopensBroadCertificate =
  Reopen.edgeOccurrenceCreatesReopeningObligation
    broadEdgeOccursInBroadPath

narrowScopeRevisionReopensNarrowCertificate :
  Dependency.ReopeningObligation
    (Reopen.OccurrenceDepends narrowScopeEdge narrowScopeCertificate)
    Reopen.changedEdgeInstanceArtifact
    Reopen.consequenceCertificateArtifact
narrowScopeRevisionReopensNarrowCertificate =
  Reopen.edgeOccurrenceCreatesReopeningObligation
    narrowEdgeOccursInNarrowPath

------------------------------------------------------------------------
-- The maintenance boundary is deliberately stronger than formula equality.
-- A certificate is keyed by the exact parser/semantic path that produced it;
-- reconvergence at the final Formula projection does not erase that path.
------------------------------------------------------------------------

record MaterialisedSpacyScopeReopeningBoundary : Set where
  constructor materialisedSpacyScopeReopeningBoundary
  field
    sameFinalFormulaErasesScopeHistory : Bool
    sameFinalFormulaErasesScopeHistoryIsFalse :
      sameFinalFormulaErasesScopeHistory ≡ false
    actualBroadScopeOccurrenceCanReopenItsCertificate : Bool
    actualBroadScopeOccurrenceCanReopenItsCertificateIsTrue :
      actualBroadScopeOccurrenceCanReopenItsCertificate ≡ true
    actualNarrowScopeOccurrenceCanReopenItsCertificate : Bool
    actualNarrowScopeOccurrenceCanReopenItsCertificateIsTrue :
      actualNarrowScopeOccurrenceCanReopenItsCertificate ≡ true
    formulaEqualityAloneCreatesScopeReopening : Bool
    formulaEqualityAloneCreatesScopeReopeningIsFalse :
      formulaEqualityAloneCreatesScopeReopening ≡ false
    reopeningMeansRefutation : Bool
    reopeningMeansRefutationIsFalse :
      reopeningMeansRefutation ≡ false
    reopeningChangesOriginalSpaCyParse : Bool
    reopeningChangesOriginalSpaCyParseIsFalse :
      reopeningChangesOriginalSpaCyParse ≡ false

canonicalMaterialisedSpacyScopeReopeningBoundary :
  MaterialisedSpacyScopeReopeningBoundary
canonicalMaterialisedSpacyScopeReopeningBoundary =
  materialisedSpacyScopeReopeningBoundary
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
