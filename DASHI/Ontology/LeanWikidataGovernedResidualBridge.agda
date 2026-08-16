module DASHI.Ontology.LeanWikidataGovernedResidualBridge where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Ontology.EpistemicTrit
open import DASHI.Ontology.LeanWikidataVerdictBridge
open import DASHI.Ontology.LeanWikidataSourceRegressionBridge
import DASHI.Interop.GovernedResidualOntologyLearning as Governed

------------------------------------------------------------------------
-- Existing DASHI already had the governance/safety half of residual ontology
-- learning, but intentionally left P31/P279 closure and ontology diagnostics
-- external.  James's executable Lean KB now supplies a theorem-backed producer
-- for that missing computational layer.
--
-- The adapter below does not promote Lean diagnostics to ontology truth.  It
-- converts them into the existing diagnostic-only residual/context carriers.
------------------------------------------------------------------------

sourceVerdictContext : LeanCertifiedVerdict → Governed.ContextualComparisonStatus
sourceVerdictContext verdict with positivePropositionState verdict
... | supported = Governed.contextAdmissible
... | contradicted = Governed.contextInadmissible
... | unresolved = Governed.contextUnknown

supportedSourceContextAdmissible :
  sourceVerdictContext artistUnionVerdict ≡ Governed.contextAdmissible
supportedSourceContextAdmissible = refl

certifiedNegativeContextInadmissible :
  sourceVerdictContext badAlignmentVerdict ≡ Governed.contextInadmissible
certifiedNegativeContextInadmissible = refl

------------------------------------------------------------------------
-- A source diagnostic becomes an existing ResidualFeatureReceipt.  The
-- diagnosticOnly field is fixed to true by construction, preserving the old
-- governance theorem rather than bypassing it.
------------------------------------------------------------------------

residualFromLeanVerdict :
  LeanCertifiedVerdict →
  Governed.ResidualFeatureKind →
  String → String → String →
  Governed.ResidualFeatureReceipt
residualFromLeanVerdict verdict kind focal coverage feature =
  Governed.residualFeatureReceipt
    focal
    kind
    coverage
    (propositionLabel verdict)
    (sourceVerdictContext verdict)
    feature
    true
    refl

brokenKbAncestryResidual : Governed.ResidualFeatureReceipt
brokenKbAncestryResidual =
  residualFromLeanVerdict
    brokenKbValidityVerdict
    Governed.ancestryDeviation
    "James/Diagnostics:brokenKB"
    "aristotle:ae06ae06-2580-422a-8fc3-92aeaaca8762"
    "Wikidata.KB.brokenKB_cycles"

badAlignmentResidual : Governed.ResidualFeatureReceipt
badAlignmentResidual =
  residualFromLeanVerdict
    badAlignmentVerdict
    Governed.typedExcess
    "James/AlignmentExample:bad-links"
    "aristotle:ae06ae06-2580-422a-8fc3-92aeaaca8762"
    "Wikidata.AlignmentExample.bad_links_alignOk_false"

brokenKbResidualDiagnosticOnly :
  Governed.diagnosticOnly brokenKbAncestryResidual ≡ true
brokenKbResidualDiagnosticOnly = refl

badAlignmentResidualDiagnosticOnly :
  Governed.diagnosticOnly badAlignmentResidual ≡ true
badAlignmentResidualDiagnosticOnly = refl

------------------------------------------------------------------------
-- Context gating composes directly with the existing residual graph policy.
-- Explicitly rejected alignment cannot become a positive similarity edge;
-- unresolved source evidence becomes unknown-coverage rather than similarity.
------------------------------------------------------------------------

badAlignmentEdgeIsMasked :
  Governed.edgeKindForContext (sourceVerdictContext badAlignmentVerdict)
  ≡ Governed.maskedAnalogyEdge
badAlignmentEdgeIsMasked = refl

uncertifiedAlignmentVerdict : LeanCertifiedVerdict
uncertifiedAlignmentVerdict =
  leanCertifiedVerdict
    badAlignmentRejectedComputed
    "unexecuted alignment candidate"
    true
    false
    notObserved
    refs

uncertifiedAlignmentEdgeIsUnknown :
  Governed.edgeKindForContext (sourceVerdictContext uncertifiedAlignmentVerdict)
  ≡ Governed.unknownCoverageEdge
uncertifiedAlignmentEdgeIsUnknown = refl

------------------------------------------------------------------------
-- The key architectural result: adding the Lean producer strengthens the
-- evidence layer but does not alter GovernedResidualOntologyLearning's
-- authority boundary.  A source result remains incapable of applying a merge
-- or ontology mutation by itself.
------------------------------------------------------------------------

leanResidualBridgeStatement : String
leanResidualBridgeStatement =
  "James's source-matched executable ontology results populate DASHI residual and context evidence; existing governed residual learning still controls cohort admission, class/split/merge proposals, provenance transfer, and ontology mutation authority."
