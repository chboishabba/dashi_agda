module DASHI.Culture.MissingDeceasedTwentyScientistRound58RealNeighbourhoodRefinementRerunExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistRound53ParetoAcquisitionSchedulerExact as R53
import DASHI.Culture.MissingDeceasedTwentyScientistRound56ProofCarryingSchedulerFeedbackExact as R56
import DASHI.Culture.MissingDeceasedTwentyScientistRound57FirstRealAcquisitionAssessmentExact as R57
import DASHI.Law.SensibLawAdaptiveLegalResearchFeedbackLoopExact as Feedback
import DASHI.Law.SensibLawProofSearchResultAssessmentExact as Assessment

------------------------------------------------------------------------
-- ROUND 58: REAL NEIGHBOURHOOD REFINEMENT -> PARETO RERUN
--
-- A second real public source refines the Chavez/Scorpius/DARHT acquisition
-- neighbourhood without paying H2.  The source is LA-UR-24-29354, proceedings
-- of the October 11, 2023 LANL workshop "Multi-Probe Radiography: For 2035 and
-- Beyond".  Relevant public statements include:
--
-- * Mike Furlanetto presented "ASD Scorpius – A New Tool to Validate Primary
--   Performance";
-- * Scorpius component design/development is described as a joint effort among
--   LANL, Sandia, LLNL and NNSS;
-- * Alex Press presented "Multi-Pulse Test Line for Beam-Target Interaction
--   Studies at DARHT";
-- * the proposed DARHT test stand would redirect the beam for measurements,
--   with a bend/focus magnet design underway.
--
-- These facts narrow the producer/object search space.  They do not identify a
-- second retained scientist and do not prove that any unnamed registrant was
-- present or involved.
------------------------------------------------------------------------

record NeighbourhoodRefinementReceipt : Set where
  constructor neighbourhood-refinement-receipt
  field
    sourceOwner : String
    nativeLocator : String
    sourceIdentifier : String
    sourceDate : String
    sourceTitle : String
    exactPaidFacts : String
    narrowedProducerSurface : String
    boundedAbsenceReference : String
    scopeBoundary : String

open NeighbourhoodRefinementReceipt public

scorpiusWorkshopProceedingsReceipt : NeighbourhoodRefinementReceipt
scorpiusWorkshopProceedingsReceipt = neighbourhood-refinement-receipt
  "Los Alamos National Laboratory / OSTI public proceedings carrier"
  "https://www.osti.gov/servlets/purl/2439165"
  "LA-UR-24-29354"
  "2024-08-29; proceedings describe workshop held 2023-10-11"
  "Multi-Probe Radiography: For 2035 and Beyond"
  "Mike Furlanetto is named for the Scorpius development talk; Alex Press is named for the DARHT Multi-Pulse Test Line talk; Scorpius component design/development is described as joint LANL/Sandia/LLNL/NNSS work; DARHT test-line bend/focus magnet design is described as underway"
  "named presenters + LANL/Sandia/LLNL/NNSS component-development paths + DARHT test-line beam-bending/focusing magnet design + workshop references"
  "none of the named relevant presenters on the acquired summary surface is another retained scientist; the proceedings report over 83 registrants but do not publish a complete identity roster here"
  "the proceedings pay workshop/project-structure propositions only; they do not pay attendance identity for unnamed registrants, shared-object membership for a retained second scientist, targeting, causation, or classification"

namedScorpiusPresenterPaid : Bool
namedScorpiusPresenterPaid = true

namedDARHTMPTLPresenterPaid : Bool
namedDARHTMPTLPresenterPaid = true

jointLabDevelopmentSurfacePaid : Bool
jointLabDevelopmentSurfacePaid = true

secondRetainedScientistFromWorkshopPaid : Bool
secondRetainedScientistFromWorkshopPaid = false

workshopRegistrantCountDoesNotPayAttendanceIdentity : Bool
workshopRegistrantCountDoesNotPayAttendanceIdentity = true

jointLabProgrammeDoesNotEqualSameTask : Bool
jointLabProgrammeDoesNotEqualSameTask = true

namedPresenterDoesNotEqualCompletePersonnelRoster : Bool
namedPresenterDoesNotEqualCompletePersonnelRoster = true

------------------------------------------------------------------------
-- Real proposition-level assessment.
--
-- Unlike Round 57, the new source changes the shape of the live acquisition
-- neighbourhood: it supplies named producer/lab/task coordinates and therefore
-- narrows the remaining search space.  The H2 proposition remains unpaid.
------------------------------------------------------------------------

realNeighbourhoodNarrowingAssessment : R56.AcquisitionAssessment
realNeighbourhoodNarrowingAssessment = R56.acquisition-assessment
  R53.chavezScorpiusCrossingTask
  "OSTI/LANL LA-UR-24-29354 public workshop proceedings"
  "Scorpius and DARHT Multi-Pulse Test Line have named presenters, lab/component-development surfaces and a concrete beam-bending/focusing magnet design path that refine the Chavez exact-object search neighbourhood"
  "public LANL workshop proceedings / project-structure source"
  "acquisition-route and exact-object-neighbourhood refinement only"
  R56.admittedPayment
  Assessment.frontierNarrowed
  "generic Scorpius/DARHT H2 crossing search over task/drawing/review/work-package records"
  "refined search over Furlanetto/Press source chains, LANL-Sandia-LLNL-NNSS component records, MPTL test-stand artefacts, bend/focus magnet design records and workshop references"
  "Chavez Scorpius/DARHT exact-object scheduler neighbourhood"
  "Round 58 real admitted neighbourhood refinement; H2 unpaid but acquisition space narrowed"

realNarrowingRecomputesFrontier :
  Feedback.feedbackDisposition
    (R56.outcomePayment (R56.outcome realNeighbourhoodNarrowingAssessment))
    (R56.frontierChange realNeighbourhoodNarrowingAssessment)
  ≡ Feedback.recomputeFrontier
realNarrowingRecomputesFrontier = refl

------------------------------------------------------------------------
-- Proof-carrying rerun receipt over the real assessment.
------------------------------------------------------------------------

realNeighbourhoodRerunReceipt : R56.ProofCarryingRerunReceipt
realNeighbourhoodRerunReceipt = R56.proof-carrying-rerun-receipt
  realNeighbourhoodNarrowingAssessment
  Feedback.recomputeFrontier
  refl
  "Round-57 Chavez scheduler neighbourhood"
  "Round-58 refined Chavez scheduler neighbourhood"
  "Chavez Scorpius/DARHT exact-object scheduler neighbourhood"
  "Rounds 23-57 evidence history including LA-UR-24-27763"
  "Rounds 23-58 evidence history including LA-UR-24-27763 + LA-UR-24-29354"
  true

realRerunPreservesPriorHistory : Bool
realRerunPreservesPriorHistory = R56.priorHistoryPreserved realNeighbourhoodRerunReceipt

------------------------------------------------------------------------
-- Updated producer route.  This is a scheduler refinement, not a claim that
-- any of these sources will necessarily contain a retained-person crossing.
------------------------------------------------------------------------

round58RefinedSearchRoute : String
round58RefinedSearchRoute = "snowball Alex Press DARHT MPTL presentations/reports; Mike Furlanetto Scorpius component-development records; LANL/Sandia/LLNL/NNSS component-team documentation; MPTL bend/focus magnet design reports; workshop references and public design-review artefacts; test exact names against retained cohort only after same-object identity is established"

refinedRouteDoesNotPrejudgeCrossing : Bool
refinedRouteDoesNotPrejudgeCrossing = true

refinedRouteDoesNotAuthorizePrivatePersonnelCollection : Bool
refinedRouteDoesNotAuthorizePrivatePersonnelCollection = true

------------------------------------------------------------------------
-- Cross-round relation: Round 57 admitted a stronger exact Chavez object but
-- left the H2 frontier unchanged.  Round 58 supplies a real refinement of the
-- acquisition neighbourhood and therefore triggers a rerun while H2 stays 0.
------------------------------------------------------------------------

round57KnowledgeGainRetained : Bool
round57KnowledgeGainRetained = R57.realAcquisitionKnowledgeGainDoesNotPayH2

round58RerunDoesNotRetroactivelyPromoteRound57 : Bool
round58RerunDoesNotRetroactivelyPromoteRound57 = true

round58H2PaidCount : Nat
round58H2PaidCount = 0

round58H3PaidCount : Nat
round58H3PaidCount = 0

round58Reading : String
round58Reading = "A second real acquisition now exercises the feedback loop. LA-UR-24-29354 narrows the Chavez/Scorpius/DARHT acquisition neighbourhood by naming Mike Furlanetto for Scorpius, Alex Press for the DARHT Multi-Pulse Test Line, the LANL/Sandia/LLNL/NNSS joint component-development surface, and a concrete MPTL beam-bending/focusing magnet design path. This admitted source changes the search producer space and therefore triggers a Pareto recomputation. No second retained scientist is paid; the workshop's >83 registrants do not become an attendance roster; H2/H3 remain zero."

round58Next : String
round58Next = "Rerun the local Chavez Pareto neighbourhood using the refined producer routes. Prefer exact MPTL magnet/test-stand reports, Scorpius component-team artefacts and public design-review records over generic LANL biographies. If those routes remain no-crossing, record bounded negative surfaces without upgrading them to programme-wide absence."
