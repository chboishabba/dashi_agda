module DASHI.Law.SensibLawYindjibarndiFiniteCutRecomputeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (primStringEquality)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawFiniteExecutableLegalSearchExact as Search
import DASHI.Cognition.PNF.SensibLawFiniteLegalCutGuardExact as CutGuard

------------------------------------------------------------------------
-- M8.1 LIVE FINITE-CUT / RECOMPUTE EXPERIMENT
--
-- This is the finite executable projection of the source-grounded
-- Yindjibarndi adversarial packet.  It deliberately separates four snapshots:
--
--   support-only        reachable; meaningful singleton rule cut exists
--   reviewed defeat     unreachable; cut guard routes to repair
--   Mabo distinction    still unreachable because Yunupingu scope objections remain
--   candidate full repair
--                       reachable again; cut is recomputed on the new rule
--
-- The final repair is a counterfactual search candidate only.  It is not a
-- statement of current law or predicted judicial outcome.
------------------------------------------------------------------------

yindjibarndiSystem : Ontology.StableId
yindjibarndiSystem =
  Ontology.stableId "legal-system:AU.native-title.compensation"

yindjibarndiSource : Algebra.LegalSourceRef
yindjibarndiSource =
  Algebra.legal-source-ref
    (Ontology.legalSource
      (Ontology.stableId "source:Yindjibarndi:WAD37-2022")
      yindjibarndiSystem
      Ontology.caseLaw
      "Yindjibarndi compensation/acquisition adversarial source packet"
      "2025"
      "Australia / Federal Court")
    "Federal Court of Australia"
    "Yindjibarndi compensation/acquisition packet"
    "WAD37/2022"

yunupinguSupport : Algebra.LegalProposition
yunupinguSupport =
  Algebra.legal-proposition
    (Ontology.stableId "prop:Yindjibarndi:Yunupingu-support")
    Algebra.doctrinalPredicate
    (Ontology.stableId "party:Yindjibarndi-applicant")
    (Ontology.stableId "issue:s51xxxi-acquisition")
    yindjibarndiSystem
    "Applicant relies on Yunupingu in support of the acquisition route"

stateYunupinguScope : Algebra.LegalProposition
stateYunupinguScope =
  Algebra.legal-proposition
    (Ontology.stableId "prop:Yindjibarndi:State-Yunupingu-scope")
    Algebra.doctrinalPredicate
    (Ontology.stableId "party:Western-Australia")
    (Ontology.stableId "issue:Yunupingu-scope")
    yindjibarndiSystem
    "State scope objection to the proposed use of Yunupingu"

fmgYunupinguScope : Algebra.LegalProposition
fmgYunupinguScope =
  Algebra.legal-proposition
    (Ontology.stableId "prop:Yindjibarndi:FMG-Yunupingu-scope")
    Algebra.doctrinalPredicate
    (Ontology.stableId "party:FMG")
    (Ontology.stableId "issue:Yunupingu-scope")
    yindjibarndiSystem
    "FMG scope objection to the proposed use of Yunupingu"

fmgMaboAcquisition : Algebra.LegalProposition
fmgMaboAcquisition =
  Algebra.legal-proposition
    (Ontology.stableId "prop:Yindjibarndi:FMG-Mabo-acquisition")
    Algebra.doctrinalPredicate
    (Ontology.stableId "party:FMG")
    (Ontology.stableId "issue:Mabo-acquisition-distinction")
    yindjibarndiSystem
    "FMG Mabo acquisition objection recorded in the source packet"

compensableAcquisitionCandidate : Algebra.LegalProposition
compensableAcquisitionCandidate =
  Algebra.legal-proposition
    (Ontology.stableId "prop:Yindjibarndi:compensable-acquisition-candidate")
    Algebra.doctrinalPredicate
    (Ontology.stableId "party:Yindjibarndi-applicant")
    (Ontology.stableId "issue:s51xxxi-acquisition")
    yindjibarndiSystem
    "candidate compensable-acquisition route; not an adjudicative conclusion"

------------------------------------------------------------------------
-- Snapshot A: support route, before reviewed defeaters are admitted.
------------------------------------------------------------------------

supportRule : Algebra.LegalRule
supportRule =
  Algebra.legal-rule
    (Ontology.stableId "rule:Yindjibarndi:support-route")
    (yunupinguSupport ∷ [])
    compensableAcquisitionCandidate
    []
    (stateYunupinguScope ∷ fmgYunupinguScope ∷ fmgMaboAcquisition ∷ [])
    yindjibarndiSource
    Algebra.dashReconstructionRole
    "candidate-only reconstruction"
    "Australia / Yindjibarndi compensation issue"

supportGraph : Algebra.LegalGraph
supportGraph =
  Algebra.legal-graph
    (supportRule ∷ [])
    (yindjibarndiSource ∷ [])

supportFacts : Algebra.FactSet
supportFacts =
  Algebra.fact-set
    (yunupinguSupport ∷ [])

supportRouteReachable :
  Search.reachable 1 supportGraph supportFacts compensableAcquisitionCandidate
  ≡ true
supportRouteReachable = refl

supportRouteMinimalCut :
  CutGuard.searchReachableMinimalCut
    1 supportGraph supportFacts compensableAcquisitionCandidate
  ≡ Search.found (Search.ruleKey supportRule ∷ [])
supportRouteMinimalCut = refl

------------------------------------------------------------------------
-- Snapshot B: all three reviewed defeaters are admitted.
------------------------------------------------------------------------

defeatedFacts : Algebra.FactSet
defeatedFacts =
  Algebra.fact-set
    (stateYunupinguScope ∷
     fmgYunupinguScope ∷
     fmgMaboAcquisition ∷
     yunupinguSupport ∷ [])

defeatedRouteUnreachable :
  Search.reachable 1 supportGraph defeatedFacts compensableAcquisitionCandidate
  ≡ false
defeatedRouteUnreachable = refl

defeatedRouteHasNoMeaningfulCut :
  CutGuard.searchReachableMinimalCut
    1 supportGraph defeatedFacts compensableAcquisitionCandidate
  ≡ Search.notFound
defeatedRouteHasNoMeaningfulCut = refl

------------------------------------------------------------------------
-- Snapshot C: exact Mabo distinction repairs only the Mabo objection.
-- The candidate refined rule deliberately retains both Yunupingu scope
-- defeaters, so the route remains unreachable.
------------------------------------------------------------------------

maboDistinguishedRule : Algebra.LegalRule
maboDistinguishedRule =
  Algebra.legal-rule
    (Ontology.stableId "rule:Yindjibarndi:after-Mabo-distinction")
    (yunupinguSupport ∷ [])
    compensableAcquisitionCandidate
    []
    (stateYunupinguScope ∷ fmgYunupinguScope ∷ [])
    yindjibarndiSource
    Algebra.dashReconstructionRole
    "candidate-only exact Mabo counter-defeat"
    "Australia / Yindjibarndi compensation issue"

maboDistinguishedGraph : Algebra.LegalGraph
maboDistinguishedGraph =
  Algebra.legal-graph
    (maboDistinguishedRule ∷ [])
    (yindjibarndiSource ∷ [])

maboDistinguishedFacts : Algebra.FactSet
maboDistinguishedFacts =
  Algebra.fact-set
    (stateYunupinguScope ∷
     fmgYunupinguScope ∷
     yunupinguSupport ∷ [])

maboRepairStillUnreachable :
  Search.reachable
    1 maboDistinguishedGraph maboDistinguishedFacts
    compensableAcquisitionCandidate
  ≡ false
maboRepairStillUnreachable = refl

maboRepairStillRoutesToFurtherRepair :
  CutGuard.searchReachableMinimalCut
    1 maboDistinguishedGraph maboDistinguishedFacts
    compensableAcquisitionCandidate
  ≡ Search.notFound
maboRepairStillRoutesToFurtherRepair = refl

------------------------------------------------------------------------
-- Snapshot D: counterfactual complete repair candidate.
--
-- This snapshot exists only to test recomputation.  It removes the remaining
-- encoded defeaters from the candidate route; it does not assert that source
-- review has actually paid those objections.
------------------------------------------------------------------------

fullyRepairedCandidateRule : Algebra.LegalRule
fullyRepairedCandidateRule =
  Algebra.legal-rule
    (Ontology.stableId "rule:Yindjibarndi:fully-repaired-candidate")
    (yunupinguSupport ∷ [])
    compensableAcquisitionCandidate
    []
    []
    yindjibarndiSource
    Algebra.dashReconstructionRole
    "counterfactual finite-cut recompute candidate only"
    "Australia / Yindjibarndi compensation issue"

fullyRepairedCandidateGraph : Algebra.LegalGraph
fullyRepairedCandidateGraph =
  Algebra.legal-graph
    (fullyRepairedCandidateRule ∷ [])
    (yindjibarndiSource ∷ [])

fullyRepairedCandidateFacts : Algebra.FactSet
fullyRepairedCandidateFacts =
  Algebra.fact-set
    (yunupinguSupport ∷ [])

fullyRepairedCandidateReachable :
  Search.reachable
    1 fullyRepairedCandidateGraph fullyRepairedCandidateFacts
    compensableAcquisitionCandidate
  ≡ true
fullyRepairedCandidateReachable = refl

recomputedMinimalCut :
  CutGuard.searchReachableMinimalCut
    1 fullyRepairedCandidateGraph fullyRepairedCandidateFacts
    compensableAcquisitionCandidate
  ≡ Search.found (Search.ruleKey fullyRepairedCandidateRule ∷ [])
recomputedMinimalCut = refl

cutIdentityActuallyChanges :
  primStringEquality
    (Search.ruleKey supportRule)
    (Search.ruleKey fullyRepairedCandidateRule)
  ≡ false
cutIdentityActuallyChanges = refl

------------------------------------------------------------------------
-- Recompute / non-promotion boundary.
------------------------------------------------------------------------

data OldCutMayBeReusedAfterRefinementWithoutRecompute : Set where
data PartialMaboRepairMakesRouteReachable : Set where
data FullyRepairedCandidateIsCurrentLaw : Set where
data FiniteCutPredictsJudicialOutcome : Set where

oldCutCannotBeFrozenAcrossRefinement :
  OldCutMayBeReusedAfterRefinementWithoutRecompute → ⊥
oldCutCannotBeFrozenAcrossRefinement ()

partialMaboRepairDoesNotReopen :
  PartialMaboRepairMakesRouteReachable → ⊥
partialMaboRepairDoesNotReopen ()

fullyRepairedCandidateDoesNotBecomeLaw :
  FullyRepairedCandidateIsCurrentLaw → ⊥
fullyRepairedCandidateDoesNotBecomeLaw ()

finiteCutDoesNotPredictOutcome :
  FiniteCutPredictsJudicialOutcome → ⊥
finiteCutDoesNotPredictOutcome ()

record YindjibarndiFiniteCutRecomputeBoundary : Set where
  constructor yindjibarndiFiniteCutRecomputeBoundary
  field
    supportSnapshotHasMeaningfulCut : Bool
    supportSnapshotHasMeaningfulCutIsTrue :
      supportSnapshotHasMeaningfulCut ≡ true

    defeatedSnapshotRoutesToRepair : Bool
    defeatedSnapshotRoutesToRepairIsTrue :
      defeatedSnapshotRoutesToRepair ≡ true

    maboOnlyRepairStillRoutesToRepair : Bool
    maboOnlyRepairStillRoutesToRepairIsTrue :
      maboOnlyRepairStillRoutesToRepair ≡ true

    fullyRepairedCandidateRecomputesCut : Bool
    fullyRepairedCandidateRecomputesCutIsTrue :
      fullyRepairedCandidateRecomputesCut ≡ true

    recomputedCutIdentityChanges : Bool
    recomputedCutIdentityChangesIsTrue :
      recomputedCutIdentityChanges ≡ true

    recomputedCutCreatesCurrentLaw : Bool
    recomputedCutCreatesCurrentLawIsFalse :
      recomputedCutCreatesCurrentLaw ≡ false

open YindjibarndiFiniteCutRecomputeBoundary public

canonicalYindjibarndiFiniteCutRecomputeBoundary :
  YindjibarndiFiniteCutRecomputeBoundary
canonicalYindjibarndiFiniteCutRecomputeBoundary =
  yindjibarndiFiniteCutRecomputeBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
