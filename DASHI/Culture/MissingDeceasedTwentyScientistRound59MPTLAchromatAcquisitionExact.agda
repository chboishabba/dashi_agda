module DASHI.Culture.MissingDeceasedTwentyScientistRound59MPTLAchromatAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistRound53ParetoAcquisitionSchedulerExact as R53
import DASHI.Culture.MissingDeceasedTwentyScientistRound56ProofCarryingSchedulerFeedbackExact as R56
import DASHI.Culture.MissingDeceasedTwentyScientistRound58RealNeighbourhoodRefinementRerunExact as R58
import DASHI.Law.SensibLawAdaptiveLegalResearchFeedbackLoopExact as Feedback
import DASHI.Law.SensibLawProofSearchResultAssessmentExact as Assessment

------------------------------------------------------------------------
-- ROUND 59: DARHT MULTI-PULSE TEST LINE ACHROMAT ACQUISITION
--
-- Real public technical carrier:
--   LA-UR-22-21508, M. Schulze, 2022-02-10,
--   "Achromat Design for Multi-Pulse Test Line".
--
-- The report describes an independent DARHT-II MPTL endpoint station and a
-- preliminary 90-degree achromatic bending section consisting of two 45-degree
-- dipoles plus a focusing quadrupole.  This sharpens the Round-58 workshop
-- statement that a bend/focus magnet design was underway.
--
-- Important boundary: the currently acquired surfaces do not yet pay that the
-- Alex Press workshop talk and LA-UR-22-21508 are the same exact document/design
-- revision, nor do they name a second retained scientist on the exact achromat
-- carrier.  Compatibility / likely technical lineage is not same-object proof.
------------------------------------------------------------------------

record MPTLAchromatReceipt : Set where
  constructor mptl-achromat-receipt
  field
    sourceOwner : String
    nativeLocator : String
    sourceIdentifier : String
    sourceDate : String
    sourceTitle : String
    namedAuthor : String
    exactTechnicalObject : String
    exactPaidProposition : String
    workshopCompatibilityReference : String
    exactWorkshopToReportWeldPaid : Bool
    secondRetainedPersonOnExactCarrier : Bool
    scopeBoundary : String

open MPTLAchromatReceipt public

mptlAchromatReceipt : MPTLAchromatReceipt
mptlAchromatReceipt = mptl-achromat-receipt
  "Los Alamos National Laboratory / OSTI public technical report carrier"
  "https://www.osti.gov/servlets/purl/1846874"
  "LA-UR-22-21508"
  "2022-02-10"
  "Achromat Design for Multi-Pulse Test Line"
  "M. Schulze"
  "DARHT-II Multi-Pulse Test Line independent endpoint station; preliminary 90-degree achromat with two 45-degree dipoles and one focusing quadrupole"
  "A literal MPTL bend/focus magnet design object existed by February 2022 with a named technical author and specified optical/electromechanical design"
  "Round 58 later workshop says LANL proposed a DARHT MPTL test stand and that bend/focus magnet design was underway"
  false
  false
  "Pays the exact LA-UR-22-21508 achromat object only. It does not by itself identify Alex Press as author/participant in that report, weld the workshop statement to this exact revision, identify a second retained scientist, or establish any causal/targeting claim."

mptlExactObjectPaid : Bool
mptlExactObjectPaid = true

mptlSecondRetainedPersonPaid : Bool
mptlSecondRetainedPersonPaid = secondRetainedPersonOnExactCarrier mptlAchromatReceipt

mptlWorkshopToReportSameObjectPaid : Bool
mptlWorkshopToReportSameObjectPaid = exactWorkshopToReportWeldPaid mptlAchromatReceipt

mptlMagnetProducerNarrowed : Bool
mptlMagnetProducerNarrowed = true

------------------------------------------------------------------------
-- Proof-carrying scheduler assessment.
--
-- This is a real admitted knowledge gain that narrows the Chavez/DARHT/MPTL
-- acquisition neighbourhood, but does not close the H2 crossing residual.
------------------------------------------------------------------------

mptlAssessment : R56.AcquisitionAssessment
mptlAssessment = R56.acquisition-assessment
  R53.chavezScorpiusCrossingTask
  "OSTI/LANL LA-UR-22-21508"
  "M. Schulze authored an exact DARHT-II MPTL 90-degree achromat design with two 45-degree dipoles and a focusing quadrupole"
  "primary-like public LANL technical report carrier"
  "exact MPTL achromat design/object proposition only"
  R56.admittedPayment
  Assessment.frontierNarrowed
  "Round 58: named presenters/labs + generic MPTL bend/focus magnet design path"
  "Round 59: exact MPTL achromat report ID, named author, dipole/quadrupole architecture; workshop-to-report weld and retained crossing still unpaid"
  "DARHT MPTL / achromat / beam-bending magnet producer neighbourhood"
  "Round 59 real LA-UR-22-21508 acquisition assessment"

mptlFeedbackRecomputes :
  Feedback.feedbackDisposition
    (R56.outcomePayment (R56.outcome mptlAssessment))
    (R56.frontierChange mptlAssessment)
  ≡ Feedback.recomputeFrontier
mptlFeedbackRecomputes = refl

------------------------------------------------------------------------
-- New residual / next discriminator.
------------------------------------------------------------------------

mptlNextResidual : String
mptlNextResidual = "Acquire an identity-bearing citation, design review, drawing, later MPTL technical report, or workshop support record that explicitly connects Alex Press / the 2023 MPTL presentation to LA-UR-22-21508 or its achromat hardware, then inspect the resulting personnel/design-review surface for a retained-person crossing."

mptlNoCrossingDoesNotProveNoCrossingAnywhere : Bool
mptlNoCrossingDoesNotProveNoCrossingAnywhere = true

compatibleTechnicalDescriptionsDoNotPaySameRevisionIdentity : Bool
compatibleTechnicalDescriptionsDoNotPaySameRevisionIdentity = true

namedAuthorDoesNotCreateWorkshopAttendance : Bool
namedAuthorDoesNotCreateWorkshopAttendance = true

mptlExactObjectDoesNotPayH2 : Bool
mptlExactObjectDoesNotPayH2 = true

mptlExactObjectDoesNotPayH3 : Bool
mptlExactObjectDoesNotPayH3 = true

round59H2PaidCount : Nat
round59H2PaidCount = 0

round59H3PaidCount : Nat
round59H3PaidCount = 0

round59Reading : String
round59Reading = "The Pareto acquisition loop has resolved the generic Round-58 'bend/focus magnet design underway' lead into a literal public MPTL achromat object: LA-UR-22-21508 by M. Schulze, specifying the DARHT-II independent endpoint station and a 90-degree achromat built from two 45-degree dipoles plus a focusing quadrupole. This is admitted real knowledge gain and narrows the producer/object fibre, so the local scheduler recomputes. The acquired record does not yet weld Alex Press's 2023 workshop presentation to this exact report/design revision and names no second retained scientist on the exact carrier. H2 and H3 therefore remain unpaid."
