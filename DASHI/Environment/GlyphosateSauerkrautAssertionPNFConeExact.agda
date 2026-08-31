module DASHI.Environment.GlyphosateSauerkrautAssertionPNFConeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Reasoning.EvidenceDesignAdmissibilityExact as Design
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone
import DASHI.Environment.GlyphosateSauerkrautBioremediationBidiExact as Kraut
import DASHI.Environment.GlyphosateSauerkrautResidualRefinementExact as Residual

------------------------------------------------------------------------
-- SHIOCTON TABLE-10 CLAIM COMPILATION
--
-- Exact values are already owned by the source-bounded glyphosate module:
-- TEG 207.26 -> 26.59 ng/g and gross difference 180.67 ng/g-equivalent.
-- This owner adds the natural-language/PNF/design/implication-cone surface.
------------------------------------------------------------------------

shioctonExactResultText : String
shioctonExactResultText =
  "At the Shiocton site, measured total effective glyphosate declined from 207.26 to 26.59 ng/g across the reported sampling dates following raw sauerkraut juice treatment."

shioctonNaturalAssertion : Cone.NaturalLanguageExperimentalAssertion
shioctonNaturalAssertion =
  Cone.naturalLanguageExperimentalAssertion
    "harle-2024-shiocton-table10-teg"
    shioctonExactResultText
    "Harle et al. 2024, Table 10"
    "reported field-result assertion"
    "source-bounded transcription into DASHI claim surface"

shioctonScope : PNF.AssertionScope
shioctonScope =
  PNF.assertionScope
    "reported Shiocton soil samples"
    "Shiocton silt-loam field site"
    "raw sauerkraut juice at the reported 140.25 L/ha application"
    "no same-time endpoint comparator is carried by the headline Table-10 contrast"
    "measured total effective glyphosate concentration"
    "12 July 2022 to 9 January 2023 reported sampling dates"

shioctonPredicates : List PNF.PredicateAtom
shioctonPredicates =
  PNF.predicateAtom
    "RSKJ-applied"
    PNF.interventionPredicate
    "field strip × treatment"
    "raw sauerkraut juice was applied at the reported field dose"
  ∷ PNF.predicateAtom
    "TEG-before"
    PNF.outcomePredicate
    "soil sample × assay × time"
    "reported pre/earlier TEG value is 207.26 ng/g"
  ∷ PNF.predicateAtom
    "TEG-after"
    PNF.outcomePredicate
    "soil sample × assay × time"
    "reported later TEG value is 26.59 ng/g"
  ∷ PNF.predicateAtom
    "different-sampling-dates"
    PNF.temporalPredicate
    "observation × time"
    "the compared values occur at different reported dates"
  ∷ PNF.predicateAtom
    "LC-MS/MS-residue-observation"
    PNF.outcomePredicate
    "soil sample × analytical method"
    "glyphosate/AMPA residue measurement is assay-mediated rather than whole hidden soil state"
  ∷ []

shioctonPNF : PNF.PredicateNormalAssertion
shioctonPNF =
  PNF.predicateNormalAssertion
    "harle-2024-shiocton-table10-teg"
    shioctonExactResultText
    PNF.studyPopulationQ
    PNF.descriptiveF
    shioctonScope
    shioctonPredicates
    "Harle et al. 2024 Table 10; bounded DASHI transcription"

shioctonCompilation : Cone.PNFCompilationReceipt shioctonNaturalAssertion
shioctonCompilation =
  Cone.pnfCompilationReceipt
    shioctonPNF
    refl
    "study-population force only; no universal transport"
    "descriptive measured-result force; treatment causation is not inserted into the root"
    "treatment, before, after, time and assay predicates exposed separately"
    "site, treatment, comparator absence, outcome and time retained explicitly"
    "manual source-bounded PNF review"

------------------------------------------------------------------------
-- Generic evidence/design receipt corresponding to the headline contrast.
------------------------------------------------------------------------

shioctonStudyDesign : Design.StudyDesignReceipt
shioctonStudyDesign =
  Design.studyDesignReceipt
    "harle-2024-shiocton-headline-residue"
    Design.observationalQuantitative
    "reported Shiocton field strips; six nominal strips, first four analysed for residue"
    "alternating treated/non-treated strips; headline Table-10 contrast itself is across sampling dates"
    "no contemporaneous endpoint comparator encoded in the headline Table-10 contrast"
    "LC-MS/MS residue analysis reported by source"
    "not an attrition design; residue-analysis subset must remain visible"
    "time, indigenous microbiome, weather/moisture, new input and sorption remain residual contributors"
    "reported RSKJ field application; treatment identity retained"
    "not promoted to a multiplicity-adjusted causal contrast"
    "207.26 -> 26.59 ng/g TEG; gross observed difference 180.67 ng/g-equivalent"
    "headline causal fraction is one-sided/partially constrained, not point-identified"
    "Shiocton site and reported interval only"
    Design.measuredSubject
    Design.validityLimited
    Design.validityLimited
    "Harle et al. 2024 Table 10 plus DASHI experimental-design audit"

shioctonEvidence : Design.EvidenceReceipt
shioctonEvidence =
  Design.evidenceReceipt
    "harle-2024-shiocton-table10-evidence"
    shioctonStudyDesign
    "Harle et al. 2024, HortScience 59(11), Table 10, DOI 10.21273/HORTSCI18041-24"
    shioctonExactResultText
    "manual extraction of source-reported values and design descriptors"
    "source values -> scaled Agda measurements -> PNF/design audit"
    "source for reported result; DASHI for logical/design interpretation"
    "headline temporal contrast does not by itself identify RSKJ-only causation or microbial mechanism"

------------------------------------------------------------------------
-- Obligation placements.
------------------------------------------------------------------------

resultObligation : PNF.AssertionObligation
resultObligation = PNF.assertionObligation
  "harle-2024-shiocton-table10-teg"
  PNF.outcomeObligation
  "are the reported before/after TEG values represented exactly at source scope?"

resultEvidenceForObligation : Design.EvidenceForObligation
resultEvidenceForObligation = Design.evidenceForObligation
  shioctonEvidence resultObligation Design.fullyAdmissible
  "Table 10 directly supplies the bounded measured values"

timeObligation : PNF.AssertionObligation
timeObligation = PNF.assertionObligation
  "harle-2024-shiocton-table10-teg"
  PNF.temporalObligation
  "are the non-contemporaneous sampling dates retained?"

timeEvidenceForObligation : Design.EvidenceForObligation
timeEvidenceForObligation = Design.evidenceForObligation
  shioctonEvidence timeObligation Design.fullyAdmissible
  "the two reported sampling dates are retained explicitly"

causalObligation : PNF.AssertionObligation
causalObligation = PNF.assertionObligation
  "harle-2024-shiocton-table10-teg"
  PNF.causalForceObligation
  "does this headline contrast identify the RSKJ-attributable causal fraction?"

causalEvidenceForObligation : Design.EvidenceForObligation
causalEvidenceForObligation = Design.evidenceForObligation
  shioctonEvidence causalObligation Design.partiallyAdmissible
  "the gross decline bounds a possible treatment-associated component, while time/control/input residuals remain open"

mechanismObligation : PNF.AssertionObligation
mechanismObligation = PNF.assertionObligation
  "harle-2024-shiocton-table10-teg"
  PNF.predicateContentObligation
  "does the result identify Lactiplantibacillus plantarum as the causal degradation mechanism?"

mechanismEvidenceForObligation : Design.EvidenceForObligation
mechanismEvidenceForObligation = Design.evidenceForObligation
  shioctonEvidence mechanismObligation Design.designMismatch
  "a field residue contrast does not isolate the microbial submechanism"

shioctonPlacements : List Cone.PredicateDesignPlacement
shioctonPlacements =
  Cone.predicateDesignPlacement
    (PNF.predicateAtom "TEG-before" PNF.outcomePredicate "soil sample × assay × time" "reported earlier TEG value is 207.26 ng/g")
    Cone.baselineMeasurementSlot
    resultObligation
    resultEvidenceForObligation
    "Table-10 baseline/result coordinate"
  ∷ Cone.predicateDesignPlacement
    (PNF.predicateAtom "TEG-after" PNF.outcomePredicate "soil sample × assay × time" "reported later TEG value is 26.59 ng/g")
    Cone.endpointMeasurementSlot
    resultObligation
    resultEvidenceForObligation
    "Table-10 endpoint/result coordinate"
  ∷ Cone.predicateDesignPlacement
    (PNF.predicateAtom "different-sampling-dates" PNF.temporalPredicate "observation × time" "the compared values occur at different reported dates")
    Cone.timeSlot
    timeObligation
    timeEvidenceForObligation
    "temporal coordinate retained rather than erased"
  ∷ Cone.predicateDesignPlacement
    (PNF.predicateAtom "RSKJ-attributable" PNF.causalPredicate "treatment × residue change" "incremental causal attribution to RSKJ")
    Cone.causalIdentificationSlot
    causalObligation
    causalEvidenceForObligation
    "only a residual envelope is admissible from the headline contrast"
  ∷ Cone.predicateDesignPlacement
    (PNF.predicateAtom "LAB-mechanism" PNF.causalPredicate "microbial mechanism × glyphosate transformation" "Lactiplantibacillus plantarum is the causal degradation mechanism")
    Cone.mechanismIdentificationSlot
    mechanismObligation
    mechanismEvidenceForObligation
    "mechanism remains unisolated"
  ∷ []

shioctonDesignMap : Cone.AssertionDesignMap shioctonNaturalAssertion
shioctonDesignMap = Cone.assertionDesignMap
  shioctonCompilation
  shioctonPlacements
  "measured result/time are direct; causal attribution is partial; mechanism identification is unsupported by this contrast"
  "contemporaneous endpoint counterfactual, full nuisance ledger and mechanism-specific intervention/assay remain open"

------------------------------------------------------------------------
-- Implication nodes.
------------------------------------------------------------------------

measuredDeclineAssertion : PNF.PredicateNormalAssertion
measuredDeclineAssertion = shioctonPNF

boundedCausalEnvelopeAssertion : PNF.PredicateNormalAssertion
boundedCausalEnvelopeAssertion =
  PNF.predicateNormalAssertion
    "shiocton-bounded-rskj-contribution"
    "The Shiocton gross TEG decline supplies a one-sided envelope on the possible RSKJ-attributable contribution after explicit residual accounting."
    PNF.studyPopulationQ
    PNF.associationalF
    shioctonScope
    (PNF.predicateAtom "bounded-attribution" PNF.causalPredicate "treatment × observed decline × residual ledger" "causal component remains inside an admissible residual envelope" ∷ [])
    "DASHI inference from source values plus residual-bound architecture"

fullCausalAssertion : PNF.PredicateNormalAssertion
fullCausalAssertion =
  PNF.predicateNormalAssertion
    "shiocton-full-rskj-causation"
    "Raw sauerkraut juice caused the full reported Shiocton TEG decline."
    PNF.studyPopulationQ
    PNF.causalF
    shioctonScope
    (PNF.predicateAtom "full-causal-attribution" PNF.causalPredicate "RSKJ × TEG decline" "all gross observed decline is attributed to RSKJ" ∷ [])
    "candidate promotion; not established by headline contrast"

labMechanismAssertion : PNF.PredicateNormalAssertion
labMechanismAssertion =
  PNF.predicateNormalAssertion
    "shiocton-lab-mechanism"
    "Lactiplantibacillus plantarum in raw sauerkraut juice caused the observed glyphosate degradation."
    PNF.studyPopulationQ
    PNF.causalF
    shioctonScope
    (PNF.predicateAtom "LAB-causes-degradation" PNF.causalPredicate "LAB × glyphosate transformation" "specific introduced LAB mechanism causes the measured residue loss" ∷ [])
    "candidate mechanism promotion; no exact mechanism receipt installed"

rootNode : Cone.ImplicationNode
rootNode = Cone.implicationNode
  "measured-shiocton-teg-decline"
  measuredDeclineAssertion
  "direct bounded measured-result node"

boundedNode : Cone.ImplicationNode
boundedNode = Cone.implicationNode
  "bounded-rskj-causal-envelope"
  boundedCausalEnvelopeAssertion
  "qualified backward BIDI consequence using gross difference and explicit residuals"

fullCausalNode : Cone.ImplicationNode
fullCausalNode = Cone.implicationNode
  "full-rskj-causal-effect"
  fullCausalAssertion
  "stronger causal attribution requiring a contemporaneous/control identification receipt"

labNode : Cone.ImplicationNode
labNode = Cone.implicationNode
  "specific-lab-mechanism"
  labMechanismAssertion
  "specific microbial mechanism requiring independent mechanism evidence"

shioctonCone : Cone.ExperimentalImplicationCone shioctonNaturalAssertion
shioctonCone = Cone.experimentalImplicationCone
  shioctonDesignMap
  rootNode
  (rootNode ∷ boundedNode ∷ fullCausalNode ∷ labNode ∷ [])
  ( Cone.implicationEdge
      "measured-shiocton-teg-decline"
      "bounded-rskj-causal-envelope"
      Cone.derivesResidualEnvelope
      Cone.qualifiedEdge
      "gross difference 180.67 ng/g-equivalent plus one-sided residual envelope"
      "elapsed-time, indigenous microbiome, weather/moisture, assay, new-input and sorption residuals remain explicit"
  ∷ Cone.implicationEdge
      "measured-shiocton-teg-decline"
      "full-rskj-causal-effect"
      Cone.attributesCausalEffect
      Cone.blockedEdge
      "headline contrast lacks the required same-time causal identification receipt"
      "gross decline cannot be equated with treatment-only effect"
  ∷ Cone.implicationEdge
      "bounded-rskj-causal-envelope"
      "specific-lab-mechanism"
      Cone.identifiesMechanism
      Cone.blockedEdge
      "no mechanism-isolation receipt identifies introduced LAB as the unique cause"
      "indigenous microbes, chemistry/sorption and combined mechanisms remain live"
  ∷ [])
  "safe cone reaches the exact measured result and the explicitly qualified residual causal envelope"
  "blocked cone retains full RSKJ causation and specific LAB mechanism until new design/evidence receipts are installed"

------------------------------------------------------------------------
-- Exact source arithmetic remains connected to the cone root.
------------------------------------------------------------------------

shioctonGrossDifferenceStillExact :
  Residual.shioctonGrossDifference + 2659 ≡ 20726
shioctonGrossDifferenceStillExact = Residual.shioctonGrossDifferenceCloses

record GlyphosateAssertionConeBoundary : Set where
  constructor glyphosateAssertionConeBoundary
  field
    tableResultIsCausalEffectByDefinition : Bool
    tableResultIsCausalEffectByDefinitionIsFalse :
      tableResultIsCausalEffectByDefinition ≡ false
    boundedResidualEnvelopeIsStillAnImplication : Bool
    boundedResidualEnvelopeIsStillAnImplicationIsTrue :
      boundedResidualEnvelopeIsStillAnImplication ≡ true
    fullCausalAttributionIsBlocked : Bool
    fullCausalAttributionIsBlockedIsTrue :
      fullCausalAttributionIsBlocked ≡ true
    specificLABMechanismIsBlocked : Bool
    specificLABMechanismIsBlockedIsTrue :
      specificLABMechanismIsBlocked ≡ true

canonicalGlyphosateAssertionConeBoundary : GlyphosateAssertionConeBoundary
canonicalGlyphosateAssertionConeBoundary =
  glyphosateAssertionConeBoundary false refl true refl true refl true refl
