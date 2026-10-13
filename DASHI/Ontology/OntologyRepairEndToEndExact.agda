module DASHI.Ontology.OntologyRepairEndToEndExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Integer using (+_)

import DASHI.Cognition.PNF.TypePressure as PNF
import DASHI.Cognition.PNF.WikidataRepairProposal as Repair
import DASHI.Core.QueryFactorisationSufficiency as Factor
import DASHI.Ontology.OntologyRepairCompletionExact as Completion
import DASHI.Ontology.OntologyRepairPluralityMaxCutExact as Plural
import DASHI.Ontology.RosarioPNFAdmissibleFactorisationExact as RosarioGov

------------------------------------------------------------------------
-- CANONICAL END-TO-END DEMONSTRATOR
------------------------------------------------------------------------

questions :
  Factor.InquiryQuestionFamily RosarioGov.AlignmentState RosarioGov.AlignmentQuery
questions = RosarioGov.alignmentQuestions

projection : RosarioGov.AlignmentState → RosarioGov.AlignmentSurface
projection = RosarioGov.coarseAlignmentSurface

query : RosarioGov.AlignmentQuery
query = RosarioGov.subclassQuery

disjointnessQuery : RosarioGov.AlignmentQuery
disjointnessQuery = RosarioGov.disjointnessQuery

mappingEvidence : Plural.PluralRepairEvidence
mappingEvidence =
  Plural.pluralRepairEvidence
    Plural.mappingOrigin
    "lgbtDB Q5051 oldid 343950 -> Wikidata Q220505 equivalent-class observation"
    "lgbtDB pinned revision 343950"
    "film-festival mapping review"

llmEvidence : Plural.PluralRepairEvidence
llmEvidence =
  Plural.pluralRepairEvidence
    Plural.llmOrigin
    "Rosario-style semantic diagnostic contribution; diagnostic only"
    "Rosario/OCTF attribution surface"
    "bounded ontology-review consumer"

humanEvidence : Plural.PluralRepairEvidence
humanEvidence =
  Plural.pluralRepairEvidence
    Plural.humanReviewOrigin
    "human review acknowledges mapping as evidence without asserting equivalence truth"
    "DASHI review receipt"
    "bounded ontology-review consumer"

mappingPressure :
  Plural.PluralPressureContribution "lgbtDB:Q5051" "Wikidata:Q220505"
mappingPressure =
  Plural.mkPluralPressure "lgbtDB:Q5051" "Wikidata:Q220505" mappingEvidence (+ 1)

llmPressure :
  Plural.PluralPressureContribution "lgbtDB:Q5051" "Wikidata:Q220505"
llmPressure =
  Plural.mkPluralPressure "lgbtDB:Q5051" "Wikidata:Q220505" llmEvidence (+ 0)

humanPressure :
  Plural.PluralPressureContribution "lgbtDB:Q5051" "Wikidata:Q220505"
humanPressure =
  Plural.mkPluralPressure "lgbtDB:Q5051" "Wikidata:Q220505" humanEvidence (+ 1)

canonicalPluralEnvelope :
  Plural.PluralPressureEnvelope "lgbtDB:Q5051" "Wikidata:Q220505"
canonicalPluralEnvelope =
  PNF.typePressureEnvelope (mappingPressure ∷ llmPressure ∷ humanPressure ∷ [])

canonicalReviewEvidence : Repair.RepairEvidence
canonicalReviewEvidence = Completion.filmFestivalReviewEvidence

canonicalReviewProposal : Repair.RepairProposal
canonicalReviewProposal =
  Completion.compileEvidenceSensitiveRepair
    (Repair.target Completion.filmFestivalReviewProposal)
    Completion.unresolvedFinding
    Completion.pluralReviewedEvidence
    canonicalReviewEvidence

record EndToEndCase : Set where
  constructor endToEndCase
  field
    fixtureObjectId : String
    plurality : Plural.PluralPressureEnvelope "lgbtDB:Q5051" "Wikidata:Q220505"
    proposal : Repair.RepairProposal
    lifecycle : Completion.LifecycleHistory
    factorisationReceipt : Factor.FactorsThrough questions projection query
    sourceReference : String
    attributionBoundary : String
open EndToEndCase public

canonicalEndToEndCase : EndToEndCase
canonicalEndToEndCase =
  endToEndCase
    Completion.realLgbtDBFilmFestivalObjectId
    canonicalPluralEnvelope
    canonicalReviewProposal
    Completion.filmFestivalLifecycle
    RosarioGov.subclassFactorsThrough
    "lgbtDB Q5051 oldid 343950; Wikidata Q220505; Rosario diagnostics kept source-bounded"
    "external observations != PNF interpretation != admissibility != edit authority"

disjointnessNonFactorisation :
  Factor.FactorsThrough questions projection disjointnessQuery → ⊥
disjointnessNonFactorisation = RosarioGov.disjointnessCannotFactorThrough
