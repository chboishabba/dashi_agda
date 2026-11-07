module DASHI.Cognition.CCDCOEP3API1998PrimaryPlanExact where

------------------------------------------------------------------------
-- PRIMARY-SOURCE GATE: 1998 API GCSCT DRAFT ACTION PLAN, AS REPRODUCED
-- IN THE CONTEMPORANEOUS APRIL 27 1998 CONGRESSIONAL RECORD.
--
-- Exact source locator:
-- https://www.govinfo.gov/content/pkg/CREC-1998-04-27/html/
-- CREC-1998-04-27-pt1-PgH2323.htm
-- Congressional Record, vol. 144 no. 48, H2323-H2327.
-- Source spans online lines 425-449, 550-560, 568-590, 599-646,
-- 652-723 and 788-795.
--
-- The primary document supports a particular draft group's planning,
-- named contributors, proposed tactics and intended measurement design.
-- It does NOT by itself show that those tactics were executed, that
-- exposures occurred, that intended outcomes changed, or that any
-- later organisation operated under one central command.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.DiscriminatorSynthesisExact as Discriminator

-- Bounded source coordinates are explicit; Agda does not fabricate an
-- external review of the original scan or assert a hash it cannot inspect.
record OriginalPlanAnchor : Set where
  constructor originalPlanAnchor
  field
    publicationLocator : String
    planDate : String
    publicationDate : String
    sourceSpan : String
    documentKind : String

sourceAnchor : OriginalPlanAnchor
sourceAnchor =
  originalPlanAnchor
    "Congressional Record 144(48), 1998-04-27, H2323-H2327; govinfo CREC-1998-04-27"
    "1998-04-03"
    "1998-04-27"
    "H2325-H2327; source rendering lines 425-795"
    "Contemporaneously reproduced draft action plan, not proof of execution"

data OriginalDocumentClaim : Set where
  draftCirculated
  contributorsNamed
  publicOpinionObjectiveStated
  mediaTacticsProposed
  scienceCenterProposed
  measurementTargetsProposed : OriginalDocumentClaim

-- Evidence that a text proposes an action is distinct from evidence
-- that the plan was authorised, funded, carried out or caused an outcome.
data HistoricalActionStage : Set where
  draftRecorded
  fundedAndApproved
  actionImplemented
  measuredOutcome : HistoricalActionStage

data ImplementationHypothesis : Set where
  unimplementedDraft
  partiallyImplemented
  fullyImplemented : ImplementationHypothesis

-- These are possible worlds compatible with the draft document's
-- existence, NOT claims about the actual history.
record PlanWorld : Set where
  constructor planWorld
  field
    implementation : ImplementationHypothesis

open PlanWorld public

unimplementedWorld : PlanWorld
unimplementedWorld = planWorld unimplementedDraft

implementedWorld : PlanWorld
implementedWorld = planWorld fullyImplemented

publicDraftObservation : PlanWorld → HistoricalActionStage
publicDraftObservation _ = draftRecorded

samePublicDraft :
  publicDraftObservation unimplementedWorld
  ≡ publicDraftObservation implementedWorld
samePublicDraft = refl

implementationDiffers :
  implementation unimplementedWorld ≡
  implementation implementedWorld → ⊥
implementationDiffers ()

draftDocumentDoesNotIdentifyImplementation :
  NF.FactorsThrough publicDraftObservation implementation → ⊥
draftDocumentDoesNotIdentifyImplementation =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      unimplementedWorld implementedWorld
      samePublicDraft implementationDiffers)

-- What an additional source-validated archive check would need to
-- distinguish: approved expenditure, dated campaign implementation,
-- or observed communication events, not merely the draft's wording.
implementationEvidenceProbe :
  Discriminator.ExperimentBundle PlanWorld
implementationEvidenceProbe =
  Discriminator.experimentBundle
    ImplementationHypothesis
    implementation
    1
    "Seek original funding/approval and executed-plan records"
    "Prospective archive test only; no executed intervention receipt available"

implementationEvidenceSeparates :
  Discriminator.BundleSeparates implementationEvidenceProbe
    unimplementedWorld implementedWorld
implementationEvidenceSeparates =
  Discriminator.bundleSeparates implementationDiffers

draftPlusImplementationEvidenceRefinesWorld :
  Discriminator.DiscriminatingLanguageExtension publicDraftObservation
draftPlusImplementationEvidenceRefinesWorld =
  Discriminator.discriminatingLanguageExtension
    (Discriminator.currentObserverCollision
      unimplementedWorld implementedWorld samePublicDraft)
    implementationEvidenceProbe
    implementationEvidenceSeparates

-- A documented strategy is already real-world evidence of a stated
-- intention by a bounded planning group. It is NOT an achieved effect.
data SupportedClaim : Set where
  draftAndProposedStrategySupported : SupportedClaim

data UnsupportedPromotion : Set where
  draftProvesExecutedCampaign
  draftProvesPopulationEffect
  draftProvesLaterUnifiedCommand : UnsupportedPromotion

noUnsupportedPromotion : UnsupportedPromotion → ⊥
noUnsupportedPromotion ()

-- The generic two-model proof is transportable, but causality and
-- downstream responsibility still need actual source/event receipts.
