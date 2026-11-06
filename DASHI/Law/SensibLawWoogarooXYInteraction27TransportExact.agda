module DASHI.Law.SensibLawWoogarooXYInteraction27TransportExact where

------------------------------------------------------------------------
-- CASE ADAPTER ONLY. The owner of the 27-cube TRANSITION is
-- DASHI.Reasoning.DialecticXYInteractionZTransportExact.
--
-- X: legal/decision-process dialectic position (T/A/S).
-- Y: independent source/ecology/response dialectic position (T/A/S).
-- Z: their interaction's own position (T/A/S).
-- These are ROLES within separately identified dialectics.
-- They are NOT nine proposition truth values or a verdict.
--
-- Claim-indexed signed P/-P evidence, contradictions, same-project
-- provenance, Pareto sources and nested decision trees live in the
-- attached fine fibre, NOT as definitions of geometric axes.
--
-- No choice of Z is justified by X,Y alone: existing comparison
-- theory retains all 27 states until an explicit rule/mediating
-- witness supplies an interaction result, which is not in the
-- current source-unpaid Woogaroo record.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Reasoning.DialecticXYInteractionZTransportExact as XY
import DASHI.Reasoning.TernaryComparisonSynthesisExact as Comparison
import DASHI.Reasoning.TernarySynthesisCellComplexExact as Cell
import DASHI.Reasoning.TernarySynthesisLogicQualificationExact as Qualifier
import DASHI.Reasoning.TrialecticThreeCellCarryDepthExact as Carry
import DASHI.Law.SensibLawWoogarooSignedPredicateFibreTreeExact as Evidence
import DASHI.Law.SensibLawWoogarooEPBC8575PleadableGroundsPrecedentCut20261028Exact as Ground

record WoogarooAttachedInteraction27 (g : Ground.Ground) : Set where
  constructor attached-interaction
  field
    xLegalDialecticRef : String
    ySourceResponseDialecticRef : String
    zInteractionRef : String

    dialecticCell : XY.DialecticEncounter27
    fineGroundEvidence : Evidence.SignedCaseFibre g

    -- Source identifiers travel with the dialectical roles.
    -- A source-unpaid witness is a *research hypothesis only*.
    sourceScopeReference : String
    candidateOnly : Bool
    candidateOnlyExact : candidateOnly ≡ true
    actualMediationReceipt : Bool
    actualMediationReceiptIsFalse : actualMediationReceipt ≡ false
open WoogarooAttachedInteraction27 public

makeHypotheticalInteraction :
  (g : Ground.Ground) →
  String → String → String →
  (x y z : XY.DialecticPosition) →
  Evidence.SignedCaseFibre g →
  WoogarooAttachedInteraction27 g
makeHypotheticalInteraction g xRef yRef zRef x y z fine =
  attached-interaction
    xRef yRef zRef
    (XY.dialectic-encounter x y z)
    fine
    (Evidence.sourceScopeRef fine)
    true refl false refl

canonicalCaseCube : ∀ {g} → WoogarooAttachedInteraction27 g →
  Cube.Ternary27Point
canonicalCaseCube interaction =
  XY.toCanonicalCube (dialecticCell interaction)

canonicalCaseComparison : ∀ {g} →
  WoogarooAttachedInteraction27 g →
  Comparison.SynthesisChoice27
canonicalCaseComparison interaction =
  XY.toCanonicalComparison27 (dialecticCell interaction)

canonicalCaseTwoCell : ∀ {g} →
  WoogarooAttachedInteraction27 g →
  Cell.LocalSynthesisTwoCell
canonicalCaseTwoCell interaction =
  Cell.choiceToTwoCell (canonicalCaseComparison interaction)

caseComparisonRetainsXY : ∀ {g} →
  (interaction : WoogarooAttachedInteraction27 g) →
  Comparison.comparisonOfSynthesis (canonicalCaseComparison interaction)
  ≡
  ( XY.positionToTri (XY.xDialecticPosition (dialecticCell interaction))
  , XY.positionToTri (XY.yDialecticPosition (dialecticCell interaction)) )
caseComparisonRetainsXY interaction = refl

caseInteractionRetainsZ : ∀ {g} →
  (interaction : WoogarooAttachedInteraction27 g) →
  Comparison.synthesisCoordinate (canonicalCaseComparison interaction)
  ≡ XY.positionToTri
      (XY.zInteractionPosition (dialecticCell interaction))
caseInteractionRetainsZ interaction = refl

caseOneCellRetainsXY : ∀ {g} →
  (interaction : WoogarooAttachedInteraction27 g) →
  Cell.originalComparisonEdge (canonicalCaseTwoCell interaction)
  ≡ Cell.comparisonOneCell
      (Comparison.comparisonOfSynthesis
        (canonicalCaseComparison interaction))
caseOneCellRetainsXY interaction =
  Cell.originalComparisonRetained (canonicalCaseComparison interaction)

caseFineEvidenceRetained : ∀ {g} →
  (interaction : WoogarooAttachedInteraction27 g) →
  Evidence.SignedCaseFibre g
caseFineEvidenceRetained = fineGroundEvidence

-- A candidate XY encounter can be displayed in each of the three
-- interaction stages without confusing the z-stage with a claim sign.
illustrativeEncounterThesis : WoogarooAttachedInteraction27
  Ground.approvedAdviceOmitted
illustrativeEncounterThesis =
  makeHypotheticalInteraction
    Ground.approvedAdviceOmitted
    "epbc:2019/8575:advice-consideration:decision-dialectic"
    "epbc:2019/8575:advice-consideration:source-response-dialectic"
    "epbc:2019/8575:advice-consideration:interaction"
    XY.thesis XY.antithesis XY.thesis
    (Evidence.unpaidFibre Ground.approvedAdviceOmitted)

illustrativeEncounterSynthesis : WoogarooAttachedInteraction27
  Ground.approvedAdviceOmitted
illustrativeEncounterSynthesis =
  makeHypotheticalInteraction
    Ground.approvedAdviceOmitted
    "epbc:2019/8575:advice-consideration:decision-dialectic"
    "epbc:2019/8575:advice-consideration:source-response-dialectic"
    "epbc:2019/8575:advice-consideration:interaction"
    XY.thesis XY.antithesis XY.synthesis
    (Evidence.unpaidFibre Ground.approvedAdviceOmitted)

sameXYDifferentZ :
  ( XY.xDialecticPosition (dialecticCell illustrativeEncounterThesis)
  , XY.yDialecticPosition (dialecticCell illustrativeEncounterThesis) )
  ≡
  ( XY.xDialecticPosition (dialecticCell illustrativeEncounterSynthesis)
  , XY.yDialecticPosition (dialecticCell illustrativeEncounterSynthesis) )
sameXYDifferentZ = refl

sameUnpaidFineEvidenceDespiteDifferentInteractionZ :
  fineGroundEvidence illustrativeEncounterThesis
  ≡ fineGroundEvidence illustrativeEncounterSynthesis
sameUnpaidFineEvidenceDespiteDifferentInteractionZ = refl

-- There is no actual authorised interaction-gluing receipt. Even
-- a perfect comparison+two-cell or same signed fibre does not provide
-- the independent higher-order trialectic face/next-depth carry.
data PaidWoogarooInteractionMediation : Set where

noPaidMediationFromShape : PaidWoogarooInteractionMediation → ⊥
noPaidMediationFromShape ()

conditionalCarryOwner : Carry.TrialecticThreeCellCarryDepthBoundary
conditionalCarryOwner = Carry.canonicalTrialecticThreeCellCarryDepthBoundary

-- This source-based carrier does not instantiate a learned, legal
-- or empirical choice of Z for each X,Y.
currentXYPairDeterminesZ : Bool
currentXYPairDeterminesZ = false
