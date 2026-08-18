module DASHI.Ontology.CrossOntologyContradictionAttributionRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Algebra.DisagreementFourViewBoundary as Four
import DASHI.Algebra.TetralemmaBridge as Tetralemma
import DASHI.Interop.WikidataDerivationFibreBridge as Fibre
import DASHI.Interop.WikidataDerivationSupportSquareExact as Square
import DASHI.Ontology.BFOContinuantOccurrentWikidataAttributionExact as BFO
import DASHI.Ontology.CrossOntologyContradictionAttributionExact as Attribution
import DASHI.Ontology.DisjointUnionLatticeJMDBridgeExact as Dun
import DASHI.Ontology.EpistemicTrit as Trit
import DASHI.Ontology.InferenceLanguageIndexedAlignmentSafetyExact as Language

supportSquareConflictRegression :
  Square.squareOutcome Square.conflictSquare ≡ Fibre.both
supportSquareConflictRegression = Square.conflictOutcomeIsBoth

supportSquareIgnoranceRegression :
  Square.squareOutcome Square.ignoranceSquare ≡ Fibre.undetermined
supportSquareIgnoranceRegression = Square.ignoranceOutcomeIsUndetermined

lossyTritRegression :
  Square.collapseSquare Square.conflictSquare ≡
  Square.collapseSquare Square.ignoranceSquare
lossyTritRegression = Square.conflictAndIgnoranceBothCollapseToUnresolved

alignmentLocalAttributionRegression :
  Four.polarPosition
    (Attribution.pooledAttributionSquare Attribution.alignmentLocalStressFibre)
  ≡ Tetralemma.both
alignmentLocalAttributionRegression = Attribution.alignmentLocalStressPositionIsBoth

alignmentLocalTritRegression :
  Attribution.pooledAttributionTrit Attribution.alignmentLocalStressFibre
  ≡ Trit.unresolved
alignmentLocalTritRegression = Attribution.alignmentLocalStressTritIsLossyUnresolved

componentFailureRegression :
  Dun.finiteDunOk Dun.missingSubclassEdge ≡ false
componentFailureRegression = Dun.componentNotSubclassOfUnionFails

exhaustivityFailureRegression :
  Dun.finiteDunOk Dun.nonExhaustiveKnownUnion ≡ false
exhaustivityFailureRegression = Dun.unionExhaustivityFailureFails

pairwiseFailureRegression :
  Dun.finiteDunOk Dun.overlappingMembers ≡ false
pairwiseFailureRegression = Dun.pairwiseDisjointnessFailureFails

subclassSafetyRegression :
  Language.safeFor Language.subclassOnlyAlignment Language.subclassLanguage ≡ true
subclassSafetyRegression = Language.subclassOnlyIsSafeForSubclassLookup

disjointnessSafetyRegression :
  Language.safeFor Language.subclassOnlyAlignment Language.disjointnessLanguage ≡ false
disjointnessSafetyRegression = Language.subclassOnlyIsNotSafeForDisjointness

literalBFOSourceRegression :
  Square.squareOutcome
    (Attribution.attributedSquare
      (Attribution.sourceEvidence BFO.bfoContinuantOccurrentAttribution))
  ≡ Fibre.satisfied
literalBFOSourceRegression = BFO.bfoSourceAxisSupported

literalBFOAlignmentOpenRegression :
  Square.squareOutcome
    (Attribution.attributedSquare
      (Attribution.alignmentEvidence BFO.bfoContinuantOccurrentAttribution))
  ≡ Fibre.undetermined
literalBFOAlignmentOpenRegression = BFO.bfoAlignmentAxisUndetermined

literalBFOMissingTransportDoesNotRefute :
  Four.polarPosition
    (Attribution.attributedSquare
      (Attribution.alignmentEvidence BFO.bfoContinuantOccurrentAttribution))
  ≡ Tetralemma.neither
literalBFOMissingTransportDoesNotRefute = BFO.bfoAlignmentMissingIsNeitherNotRefutation
