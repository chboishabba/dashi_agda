module DASHI.Ontology.LeanWikidataRelationalLensBridge where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Feed source-matched James/Aristotle Lean verdicts into the relational-lens
-- synthesis carrier without converting open-world absence into a ternary
-- decision.
--
-- Only a verdict with an explicit proof that its positive proposition state is
-- `supported` or `contradicted` enters ResolvedLeanView. `unresolved` is not
-- silently mapped to tri-mid. Aggregated support+contradiction likewise belongs
-- in the derivation-fibre/tetralemma qualification lane rather than being
-- collapsed into one trit.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import Base369 as Base
import DASHI.Ontology.EpistemicTrit as Epistemic
import DASHI.Ontology.LeanWikidataTheoremSurfaceBridge as Surface
import DASHI.Ontology.LeanWikidataVerdictBridge as Verdict
import DASHI.Reasoning.RelationalLensSynthesisCore as Lens
import DASHI.Reasoning.TernaryComparisonSynthesisExact as Synthesis

------------------------------------------------------------------------
-- Resolved source views.
------------------------------------------------------------------------

data ResolvedPolarity : Set where
  resolvedAgainst resolvedFor : ResolvedPolarity

resolvedEpistemicState : ResolvedPolarity → Epistemic.EpistemicTrit
resolvedEpistemicState resolvedAgainst = Epistemic.contradicted
resolvedEpistemicState resolvedFor = Epistemic.supported

record ResolvedLeanView : Set where
  constructor resolvedLeanView
  field
    verdict : Verdict.LeanCertifiedVerdict
    polarity : ResolvedPolarity
    resolutionExact :
      Verdict.positivePropositionState verdict
      ≡ resolvedEpistemicState polarity

open ResolvedLeanView public

resolvedLeanViewToTriTruth : ResolvedLeanView → Base.TriTruth
resolvedLeanViewToTriTruth view with polarity view
... | resolvedAgainst = Base.tri-low
... | resolvedFor = Base.tri-high

certifiedHoldsView :
  (contract : Surface.LeanTheoremContract) →
  (label : String) →
  (refs : List String) →
  ResolvedLeanView
certifiedHoldsView contract label refs =
  resolvedLeanView
    (Verdict.leanCertifiedVerdict
      contract label true true Verdict.certifiedHolds refs)
    resolvedFor
    refl

certifiedRefutedView :
  (contract : Surface.LeanTheoremContract) →
  (label : String) →
  (refs : List String) →
  ResolvedLeanView
certifiedRefutedView contract label refs =
  resolvedLeanView
    (Verdict.leanCertifiedVerdict
      contract label true true Verdict.certifiedRefuted refs)
    resolvedAgainst
    refl

certifiedHoldsQuantizesHigh :
  (contract : Surface.LeanTheoremContract) →
  (label : String) →
  (refs : List String) →
  resolvedLeanViewToTriTruth (certifiedHoldsView contract label refs)
  ≡ Base.tri-high
certifiedHoldsQuantizesHigh contract label refs = refl

certifiedRefutedQuantizesLow :
  (contract : Surface.LeanTheoremContract) →
  (label : String) →
  (refs : List String) →
  resolvedLeanViewToTriTruth (certifiedRefutedView contract label refs)
  ≡ Base.tri-low
certifiedRefutedQuantizesLow contract label refs = refl

------------------------------------------------------------------------
-- Open-world absence/source mismatch cannot inhabit a resolved view merely by
-- choosing a desired polarity.
------------------------------------------------------------------------

notObservedCannotResolveFor :
  (contract : Surface.LeanTheoremContract) →
  (label : String) →
  (refs : List String) →
  Verdict.positivePropositionState
    (Verdict.leanCertifiedVerdict
      contract label true false Verdict.notObserved refs)
  ≡ Epistemic.supported →
  ⊥
notObservedCannotResolveFor contract label refs ()

notObservedCannotResolveAgainst :
  (contract : Surface.LeanTheoremContract) →
  (label : String) →
  (refs : List String) →
  Verdict.positivePropositionState
    (Verdict.leanCertifiedVerdict
      contract label true false Verdict.notObserved refs)
  ≡ Epistemic.contradicted →
  ⊥
notObservedCannotResolveAgainst contract label refs ()

sourceMismatchCannotResolveFor :
  (contract : Surface.LeanTheoremContract) →
  (label : String) →
  (objectVerdict : Verdict.ObjectVerdict) →
  (refs : List String) →
  Verdict.positivePropositionState
    (Verdict.leanCertifiedVerdict
      contract label false true objectVerdict refs)
  ≡ Epistemic.supported →
  ⊥
sourceMismatchCannotResolveFor contract label objectVerdict refs ()

------------------------------------------------------------------------
-- Two resolved ontology lenses become an ordinary ternary comparison. The
-- synthesis coordinate is still supplied by the explicit synthesis rule.
------------------------------------------------------------------------

data LeanEvidenceLens : Set where
  leftEvidenceLens rightEvidenceLens : LeanEvidenceLens

record ResolvedLeanComparison : Set where
  constructor resolvedLeanComparison
  field
    leftView : ResolvedLeanView
    rightView : ResolvedLeanView

open ResolvedLeanComparison public

resolvedLeanProject :
  LeanEvidenceLens → ResolvedLeanComparison → ResolvedLeanView
resolvedLeanProject leftEvidenceLens comparison = leftView comparison
resolvedLeanProject rightEvidenceLens comparison = rightView comparison

resolvedLeanLensFamily :
  Lens.TernaryLensFamily
    ResolvedLeanComparison LeanEvidenceLens ResolvedLeanView
resolvedLeanLensFamily =
  Lens.ternaryLensFamily
    (Lens.lensFamily resolvedLeanProject)
    resolvedLeanViewToTriTruth

compareResolvedLeanViews :
  ResolvedLeanComparison → Synthesis.Comparison9
compareResolvedLeanViews comparison =
  Lens.compareLenses
    resolvedLeanLensFamily
    leftEvidenceLens
    rightEvidenceLens
    comparison

resolvedLeanSynthesisSystem :
  Synthesis.TotalSynthesisRule →
  Lens.LensSynthesisSystem
    ResolvedLeanComparison LeanEvidenceLens ResolvedLeanView
resolvedLeanSynthesisSystem rule =
  Lens.lensSynthesisSystem resolvedLeanLensFamily rule

synthesizeResolvedLeanViews :
  Synthesis.TotalSynthesisRule →
  ResolvedLeanComparison →
  Synthesis.SynthesisChoice27
synthesizeResolvedLeanViews rule comparison =
  Lens.synthesizeLenses
    (resolvedLeanSynthesisSystem rule)
    leftEvidenceLens
    rightEvidenceLens
    comparison

resolvedLeanSynthesisRetainsComparison :
  (rule : Synthesis.TotalSynthesisRule) →
  (comparison : ResolvedLeanComparison) →
  Synthesis.comparisonOfSynthesis
    (synthesizeResolvedLeanViews rule comparison)
  ≡ compareResolvedLeanViews comparison
resolvedLeanSynthesisRetainsComparison rule comparison =
  Lens.lensSynthesisRetainsComparison
    (resolvedLeanSynthesisSystem rule)
    leftEvidenceLens
    rightEvidenceLens
    comparison

record LeanWikidataRelationalLensBoundary : Set where
  field
    sourceMatchedResolvedVerdictsCanEnterLens : Bool
    sourceMatchedResolvedVerdictsCanEnterLensIsTrue :
      sourceMatchedResolvedVerdictsCanEnterLens ≡ true

    unresolvedAutomaticallyQuantizedToMid : Bool
    unresolvedAutomaticallyQuantizedToMidIsFalse :
      unresolvedAutomaticallyQuantizedToMid ≡ false

    bothEvidenceAutomaticallyCollapsedToTrit : Bool
    bothEvidenceAutomaticallyCollapsedToTritIsFalse :
      bothEvidenceAutomaticallyCollapsedToTrit ≡ false

    importedVerdictGainsGlobalTruthAuthority : Bool
    importedVerdictGainsGlobalTruthAuthorityIsFalse :
      importedVerdictGainsGlobalTruthAuthority ≡ false

canonicalLeanWikidataRelationalLensBoundary :
  LeanWikidataRelationalLensBoundary
canonicalLeanWikidataRelationalLensBoundary =
  record
    { sourceMatchedResolvedVerdictsCanEnterLens = true
    ; sourceMatchedResolvedVerdictsCanEnterLensIsTrue = refl
    ; unresolvedAutomaticallyQuantizedToMid = false
    ; unresolvedAutomaticallyQuantizedToMidIsFalse = refl
    ; bothEvidenceAutomaticallyCollapsedToTrit = false
    ; bothEvidenceAutomaticallyCollapsedToTritIsFalse = refl
    ; importedVerdictGainsGlobalTruthAuthority = false
    ; importedVerdictGainsGlobalTruthAuthorityIsFalse = refl
    }
