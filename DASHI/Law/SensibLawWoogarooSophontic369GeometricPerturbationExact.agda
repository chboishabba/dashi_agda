module DASHI.Law.SensibLawWoogarooSophontic369GeometricPerturbationExact where

------------------------------------------------------------------------
-- WOOGAROO 2019/8575: 369 / 27-cube geometric reasoning intervention.
--
-- Exact in-BRANCH originals:
--   Base369Ternary27HypervoxelFabricGeometryExact (T^3=27, T^9=19683)
--   Trialectic369HypervoxelUltrametricExact (A/B/C row roundtrip)
--   TrialecticThreeCellHyperformSynthesisExact (27-cell dialectic)
--   TrialecticBoundaryFaceNonfactorabilityExact (face not from edges)
--   WoogarooDialecticTrialecticSynthesis20261028Exact (case outcomes).
--
-- Geometric-reasoning / Sophontic method DONORS, separate unmerged PRs:
--   DASHI #1094/#1095 SemanticInterventionEquivarianceExact,
--   GeometricReasoningCandidateSelectionExact and SurfaceResidualExact.
--   DASHI #1265 DustNoiseSophonticMaxCut and paired perturbation evaluation.
--   Sophontic Inc., 2026: https://sophontic.ai/evals/
-- Its paired-item flip-rate protocol motivates the distinction between
-- load-bearing perturbations and nuisance perturbations. The generated
-- cases below are independent DASHI-Woogaroo FIXTURES, not Sophontic
-- benchmark samples, published performance, or trained model evidence.
--
-- IMPORTANT: Boolean-to-ternary coding uses {zero,positive}, with zero
-- meaning absent from this hypothetical fixture, NOT legal falsity.
-- The ambient T^3 contains 27 points, but this Boolean embedding only
-- visits a 2^3 subset of each row. "Cube" is a FINITE CARRIER, not a
-- physical GIS location, 3D organism, or the actual Monster 3B action.
-- Case input keeps six facts; the nine-coordinate chart adds three
-- DERIVED outputs. No geometry -> source truth / Court outcome promotion.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Reasoning.Trialectic369HypervoxelUltrametricExact as Bridge
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell
import DASHI.Reasoning.TrialecticBoundaryFaceNonfactorabilityExact as Face
import DASHI.Law.SensibLawWoogarooAdversarialLogicalTests20261028Exact as Logic
import DASHI.Law.SensibLawWoogarooDialecticTrialecticSynthesis20261028Exact as Trialectic
import DASHI.Law.SensibLawWoogarooEPBC8575PleadableGroundsPrecedentCut20261028Exact as Ground

toPositiveStatus : Bool → SSP.SSPTrit
toPositiveStatus false = SSP.sspZero
toPositiveStatus true = SSP.sspPosOne

-- A: applicant's applicable-rule / defect / materiality premises.
-- B: respondent's asserted compliance / ecology / conflict flags.
-- C: independent review gate and TWO DERIVED conditional outcomes.
applicantCube : ∀ {g} → Logic.HypotheticalWorld g → Fabric.Ternary27Point
applicantCube w =
  Fabric.ternary27Point
    (toPositiveStatus (Logic.legallyApplicable w))
    (toPositiveStatus (Logic.defectEstablished w))
    (toPositiveStatus (Logic.materialityEstablished w))

respondentCube : ∀ {g} → Logic.HypotheticalWorld g → Fabric.Ternary27Point
respondentCube w =
  Fabric.ternary27Point
    (toPositiveStatus (Logic.governmentComplianceEstablished w))
    (toPositiveStatus (Logic.ecologicalHarmAssumed w))
    (toPositiveStatus (Logic.contradictionPresent w))

reviewCube : ∀ {g} → Logic.HypotheticalWorld g → Fabric.Ternary27Point
reviewCube w =
  Fabric.ternary27Point
    (toPositiveStatus (Logic.actualEvidenceReviewed w))
    (toPositiveStatus (Logic.applicantConditional w))
    (toPositiveStatus (Logic.respondentConditional w))

worldTo369 : ∀ {g} → Logic.HypotheticalWorld g →
  Fabric.TernaryHyperformalPoint
worldTo369 w =
  Fabric.ternaryHyperformalPoint
    (applicantCube w) (respondentCube w) (reviewCube w)

-- Decode only the declared {0, +1} embedding. A raw -1 ambient
-- coordinate is NOT evidence of legal falsity; it is outside this
-- six-Boolean input image, and is mapped conservatively to false.
fromPositiveStatus : SSP.SSPTrit → Bool
fromPositiveStatus SSP.sspNegOne = false
fromPositiveStatus SSP.sspZero = false
fromPositiveStatus SSP.sspPosOne = true

positiveStatusLeftInverse : (v : Bool) →
  fromPositiveStatus (toPositiveStatus v) ≡ v
positiveStatusLeftInverse false = refl
positiveStatusLeftInverse true = refl

-- This decoder uses the six independent inputs only; the three derived
-- coordinates are readbacks that must be recomputed, not source premises.
worldFrom369 : ∀ {g} → Fabric.TernaryHyperformalPoint →
  Logic.HypotheticalWorld g
worldFrom369
  (Fabric.ternaryHyperformalPoint
    (Fabric.ternary27Point applicable defect material)
    (Fabric.ternary27Point compliant harm conflict)
    (Fabric.ternary27Point reviewed applicantResult respondentResult)) =
  Logic.world
    (fromPositiveStatus applicable)
    (fromPositiveStatus defect)
    (fromPositiveStatus material)
    (fromPositiveStatus compliant)
    (fromPositiveStatus reviewed)
    (fromPositiveStatus harm)

sixInputBitsRoundTrip : ∀ {g} (w : Logic.HypotheticalWorld g) →
  worldFrom369 (worldTo369 w) ≡ w
sixInputBitsRoundTrip
  (Logic.world applicable defect material compliant reviewed harm)
  rewrite positiveStatusLeftInverse applicable
        | positiveStatusLeftInverse defect
        | positiveStatusLeftInverse material
        | positiveStatusLeftInverse compliant
        | positiveStatusLeftInverse reviewed
        | positiveStatusLeftInverse harm = refl

-- The input embedding is injective: any two six-Boolean worlds that
-- share this exact 369 chart are identical at the input level.
-- This says nothing about legal truth, source validity, or Monster identity.
worldTo369Injective :
  ∀ {g} (left right : Logic.HypotheticalWorld g) →
  worldTo369 left ≡ worldTo369 right → left ≡ right
worldTo369Injective left right chartEqual =
  trans
    (sym (sixInputBitsRoundTrip left))
    (trans
      (cong worldFrom369 chartEqual)
      (sixInputBitsRoundTrip right))

worldToCellDialectic : ∀ {g} → Logic.HypotheticalWorld g →
  Cell.CellDialectic
worldToCellDialectic w = Cell.hyperformToCellDialectic (worldTo369 w)

geometricRoundTrip : ∀ {g} (w : Logic.HypotheticalWorld g) →
  Cell.cellDialecticToHyperform (worldToCellDialectic w)
  ≡ worldTo369 w
geometricRoundTrip w = Cell.hyperformCellDialecticRoundTrip (worldTo369 w)

observerRoundTrip : ∀ {g} (w : Logic.HypotheticalWorld g) →
  Bridge.observerToFabric (Bridge.fabricToObserver (worldTo369 w))
  ≡ worldTo369 w
observerRoundTrip w = Bridge.fabricObserverRoundTrip (worldTo369 w)

-- An explicit ambient theorem, NOT a count of empirically observed case
-- states; no claim that this input encoding spans all 19683 hypervoxels.
ambientCubeHas27States : Fabric.hypervoxelStateCount ≡ 27
ambientCubeHas27States = Fabric.hypervoxelStateCountIs27

ambientFabricHas19683States : Fabric.hyperfabricStateCount ≡ 19683
ambientFabricHas19683States = Fabric.hyperfabricStateCountIs19683

-- Semantic load-bearing pair: change only the hypothetical evidence
-- review bit, preserving every other field. Before review the applicant
-- branch cannot be promoted even with stipulated facts; after it can be
-- shortlisted for DEFEATER search, never declared a legal victory.
beforeReview : Logic.HypotheticalWorld Ground.approvedAdviceOmitted
beforeReview = Logic.world true true true false false true

afterReview : Logic.HypotheticalWorld Ground.Ground.approvedAdviceOmitted
afterReview = Logic.world true true true false true true

beforeReviewRequiresOriginals :
  Trialectic.classify beforeReview ≡ Trialectic.seekOriginals
beforeReviewRequiresOriginals = refl

afterReviewRequiresDefeaterSearch :
  Trialectic.classify afterReview
  ≡ Trialectic.applicantHypothesisForDefeaterSearch
afterReviewRequiresDefeaterSearch = refl

loadBearingPairFlipsCandidate :
  Trialectic.classify beforeReview
    ≡ Trialectic.classify afterReview → ⊥
loadBearingPairFlipsCandidate ()

-- A geometry change that DOES NOT justify a legal label flip: habitat
-- concern is not itself an advice-consideration omission. This pair
-- changes only the hypothetical ecological-harm bit.
beforeHarmOnly : Logic.HypotheticalWorld Ground.Ground.approvedAdviceOmitted
beforeHarmOnly = Logic.world true false false true true false

afterHarmOnly : Logic.HypotheticalWorld Ground.Ground.approvedAdviceOmitted
afterHarmOnly = Logic.world true false false true true true

nuisanceHarmMustNotFlipThisLegalClassification :
  Trialectic.classify beforeHarmOnly
    ≡ Trialectic.classify afterHarmOnly
nuisanceHarmMustNotFlipThisLegalClassification = refl

nuisanceChanges369Carrier :
  worldTo369 beforeHarmOnly ≡ worldTo369 afterHarmOnly → ⊥
nuisanceChanges369Carrier ()

------------------------------------------------------------------------
-- A genuinely geometric discriminator, using the already-owned T^3 grid.
--
-- The single input flip "reviewed: 0 -> 1" moves the independent cube
-- TWO adjacent steps: (0,0,0) -> (1,0,0) -> (1,1,0).
-- The first step records new review-gate status; the second records the
-- *derived* applicant shortlist. Neither step creates evidence payment.
-- The harm-only perturbation moves ONE Y step in the respondent cube,
-- although the legal outcome remains unchanged.
------------------------------------------------------------------------

reviewMiddle : Fabric.Ternary27Point
reviewMiddle =
  Fabric.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero

reviewGateStep :
  Fabric.HypervoxelAdjacent (reviewCube beforeReview) reviewMiddle
reviewGateStep = Fabric.adjacentX Fabric.zeroToPos

derivedApplicantResponseStep :
  Fabric.HypervoxelAdjacent reviewMiddle (reviewCube afterReview)
derivedApplicantResponseStep = Fabric.adjacentY Fabric.zeroToPos

nuisanceHarmSingleGridStep :
  Fabric.HypervoxelAdjacent
    (respondentCube beforeHarmOnly) (respondentCube afterHarmOnly)
nuisanceHarmSingleGridStep = Fabric.adjacentY Fabric.zeroToPos

-- Existing structured A/B/C dialectics glue three 27-cells per edge;
-- three cyclically compatible edge dialectics have SIX independent cubes
-- (A,B,C,S_AB,S_BC,S_CA) = 3^18 possible boundary states, plus the
-- separate irreducible face. This count is NOT the 3^9 case chart.
structuredTrialecticHas18TritCoordinates :
  Cell.structuredBoundaryTernaryCoordinateCount ≡ 18
structuredTrialecticHas18TritCoordinates =
  Cell.structuredBoundaryTernaryCoordinateCountIsEighteen

structuredTrialecticBoundaryHas387420489States :
  Cell.structuredBoundaryStateCount ≡ 387420489
structuredTrialecticBoundaryHas387420489States =
  Cell.structuredBoundaryStateCountIs387420489

-- Boolean contradiction is preserved, not "exploded" into either
-- finding. Independent review flag alone cannot mediate the face.
contradictoryCaseHasReconciliation :
  Trialectic.classify Logic.contradictoryWorld
    ≡ Trialectic.reconcileOpposingSourceAssertions
contradictoryCaseHasReconciliation = refl

unpaidFaceBeforeReview :
  Trialectic.trialectic
    (Trialectic.synthesise Ground.approvedAdviceOmitted beforeReview)
  ≡ Trialectic.unpaidTrialectic (Trialectic.classify beforeReview)
unpaidFaceBeforeReview = refl

unpaidFaceUnderContradiction :
  Trialectic.trialectic
    (Trialectic.synthesise Ground.approvedAdviceOmitted Logic.contradictoryWorld)
  ≡ Trialectic.unpaidTrialectic (Trialectic.classify Logic.contradictoryWorld)
unpaidFaceUnderContradiction = refl

-- NOTE: the actual attached TWO-CELL face cannot be inferred by exact
-- rechart or a paired synthetic flip. Use the existing nonfactor theorem.
sameWorldDoesNotProduceCourtAuthority :
  Trialectic.authorityIsActualCourtFinding
    (Trialectic.synthesise Ground.approvedAdviceOmitted afterReview)
  ≡ false
sameWorldDoesNotProduceCourtAuthority = refl
