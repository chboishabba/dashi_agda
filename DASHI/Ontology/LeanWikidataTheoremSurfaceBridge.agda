module DASHI.Ontology.LeanWikidataTheoremSurfaceBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import DASHI.Ontology.EpistemicTrit
open import DASHI.Ontology.LeanWikidataCertificateBridge
open import DASHI.Ontology.LeanWikidataFullSourceManifest

data LeanProofRole : Set where
  structuralTheorem checkerSoundness checkerExactness crossOntologyTheorem : LeanProofRole
  semanticExactness provenancePreservation dataModelTheorem contextPreservation : LeanProofRole
  identityTransport preservationTheorem repairSoundness diagnosticExactness : LeanProofRole
  serializationExactness negativeConstraintTheorem : LeanProofRole

record LeanTheoremContract : Set where
  constructor leanTheoremContract
  field
    source : LeanSourceModule
    theorem : String
    reading : String
    proofRole : LeanProofRole
open LeanTheoremContract public

contract0 : LeanTheoremContract
contract0 = leanTheoremContract coreSource "Wikidata.Ontology.subclassOf_trans" "subclass transitivity" structuralTheorem

contract1 : LeanTheoremContract
contract1 = leanTheoremContract coreSource "Wikidata.Ontology.instanceOf_trans_subclassOf" "instance/subclass transport" structuralTheorem

contract2 : LeanTheoremContract
contract2 = leanTheoremContract engineSource "Wikidata.KB.isSubclassOf_iff" "executable subclass checker exactness" checkerExactness

contract3 : LeanTheoremContract
contract3 = leanTheoremContract engineSource "Wikidata.KB.isInstanceOf_iff" "executable instance checker exactness" checkerExactness

contract4 : LeanTheoremContract
contract4 = leanTheoremContract disjointUnionSource "Wikidata.KB.isDisjointUnion_of_dunOk" "disjoint-union checker soundness" checkerSoundness

contract5 : LeanTheoremContract
contract5 = leanTheoremContract classAlgebraSource "Wikidata.KB.isUnion_of_unionOk" "union checker soundness" checkerSoundness

contract6 : LeanTheoremContract
contract6 = leanTheoremContract classAlgebraSource "Wikidata.KB.isIntersection_of_interOk" "intersection checker soundness" checkerSoundness

contract7 : LeanTheoremContract
contract7 = leanTheoremContract alignmentSource "Wikidata.Ontology.Alignment.subclassOf_iff" "cross-ontology alignment reflection" crossOntologyTheorem

contract8 : LeanTheoremContract
contract8 = leanTheoremContract alignmentSource "Wikidata.Ontology.Alignment.no_common_instance_of_disjoint" "disjointness preservation across alignment" crossOntologyTheorem

contract9 : LeanTheoremContract
contract9 = leanTheoremContract semanticsSource "Wikidata.Ontology.semSubclassOf_iff" "class semantics exactness" semanticExactness

contract10 : LeanTheoremContract
contract10 = leanTheoremContract semanticsSource "Wikidata.Ontology.semInstanceOf_iff" "instance semantics exactness" semanticExactness

contract11 : LeanTheoremContract
contract11 = leanTheoremContract pathsSource "Wikidata.Ontology.eval_star_p279_iff" "P279 path exactness" checkerExactness

contract12 : LeanTheoremContract
contract12 = leanTheoremContract pathsSource "Wikidata.Ontology.eval_p31_star_p279_iff" "P31/P279 path exactness" checkerExactness

contract13 : LeanTheoremContract
contract13 = leanTheoremContract provenanceSource "Wikidata.RKB.valid_sourced" "sourced projection preserves validity" provenancePreservation

contract14 : LeanTheoremContract
contract14 = leanTheoremContract provenanceSource "Wikidata.RKB.valid_reliable" "reliable projection preserves validity" provenancePreservation

contract15 : LeanTheoremContract
contract15 = leanTheoremContract ranksSource "Wikidata.Claim.not_isTruthy_deprecated" "deprecated rank excluded from truthy layer" dataModelTheorem

contract16 : LeanTheoremContract
contract16 = leanTheoremContract snaksSource "Wikidata.SnakBase.satisfiable_iff_clashFreeB" "snak satisfiability/checker exactness" checkerExactness

contract17 : LeanTheoremContract
contract17 = leanTheoremContract temporalSource "Wikidata.TKB.valid_snapshot" "temporal snapshot preserves validity" contextPreservation

contract18 : LeanTheoremContract
contract18 = leanTheoremContract typePropertiesSource "Wikidata.Profile.completeB_iff" "P1963 completeness checker exactness" checkerExactness

contract19 : LeanTheoremContract
contract19 = leanTheoremContract schemasSource "Wikidata.PKB.conformsB_iff" "schema conformance checker exactness" checkerExactness

contract20 : LeanTheoremContract
contract20 = leanTheoremContract externalIdsSource "Wikidata.IdKB.idOf_eq_some_iff_itemById_eq_some" "external-ID partial bijection" identityTransport

contract21 : LeanTheoremContract
contract21 = leanTheoremContract sitelinksSource "Wikidata.SiteKB.pageOf_eq_some_iff_itemOf_eq_some" "sitelink partial bijection" identityTransport

contract22 : LeanTheoremContract
contract22 = leanTheoremContract lexemesSource "Wikidata.LexBase.meansB_iff_instanceOf" "lexeme denotation/instance bridge" semanticExactness

contract23 : LeanTheoremContract
contract23 = leanTheoremContract itemMergeSource "Wikidata.KB.subclassOf_rename" "merge preserves subclass facts under valid rename" preservationTheorem

contract24 : LeanTheoremContract
contract24 = leanTheoremContract itemMergeSource "Wikidata.KB.instanceOf_rename" "merge preserves instance facts under valid rename" preservationTheorem

contract25 : LeanTheoremContract
contract25 = leanTheoremContract redundancySource "Wikidata.KB.dropSub_valid" "pruning redundant subclass preserves validity" repairSoundness

contract26 : LeanTheoremContract
contract26 = leanTheoremContract redundancySource "Wikidata.KB.dropSub_isSubclassOf" "pruning preserves derived subclass facts" repairSoundness

contract27 : LeanTheoremContract
contract27 = leanTheoremContract redundancySource "Wikidata.KB.dropSub_isInstanceOf" "pruning preserves derived instance facts" repairSoundness

contract28 : LeanTheoremContract
contract28 = leanTheoremContract diagnosticsSource "Wikidata.KB.errors_eq_nil_iff_valid" "diagnostic errors exactly characterize validity" diagnosticExactness

contract29 : LeanTheoremContract
contract29 = leanTheoremContract diagnosticsSource "Wikidata.KB.warning_prunable" "redundancy warning has a semantics-preserving repair" repairSoundness

contract30 : LeanTheoremContract
contract30 = leanTheoremContract rdfSource "Wikidata.Rdf.fullGraph_injective" "full RDF rendering injective/lossless" serializationExactness

contract31 : LeanTheoremContract
contract31 = leanTheoremContract rdfSource "Wikidata.Rdf.entails_sound" "RDF entailment soundness" semanticExactness

contract32 : LeanTheoremContract
contract32 = leanTheoremContract rdfSource "Wikidata.Rdf.entails_sub_iff" "RDF subclass entailment exactness" semanticExactness

contract33 : LeanTheoremContract
contract33 = leanTheoremContract rdfSource "Wikidata.Rdf.entails_inst_iff" "RDF instance entailment exactness" semanticExactness

contract34 : LeanTheoremContract
contract34 = leanTheoremContract rdfSource "Wikidata.Rdf.entails_iff_isSubclassOf" "RDF entailment equals executable subclass engine" checkerExactness

contract35 : LeanTheoremContract
contract35 = leanTheoremContract mereologySource "Wikidata.MKB.part_not_subclass" "part-of is not subclass under no-confusion boundary" negativeConstraintTheorem

contract36 : LeanTheoremContract
contract36 = leanTheoremContract mereologySource "Wikidata.MKB.part_not_instance" "part-of is not instance-of under no-confusion boundary" negativeConstraintTheorem

contract37 : LeanTheoremContract
contract37 = leanTheoremContract stratificationSource "Wikidata.KB.properSuper_wf" "proper-superclass relation well founded" structuralTheorem

contract38 : LeanTheoremContract
contract38 = leanTheoremContract stratificationSource "Wikidata.KB.topoSort_pairwise" "topological ordering respects class hierarchy" checkerSoundness

canonicalTheoremContracts : List LeanTheoremContract
canonicalTheoremContracts =
  contract0 ∷ contract1 ∷ contract2 ∷ contract3 ∷ contract4 ∷ contract5 ∷ contract6 ∷
  contract7 ∷ contract8 ∷ contract9 ∷ contract10 ∷ contract11 ∷ contract12 ∷ contract13 ∷
  contract14 ∷ contract15 ∷ contract16 ∷ contract17 ∷ contract18 ∷ contract19 ∷ contract20 ∷
  contract21 ∷ contract22 ∷ contract23 ∷ contract24 ∷ contract25 ∷ contract26 ∷ contract27 ∷
  contract28 ∷ contract29 ∷ contract30 ∷ contract31 ∷ contract32 ∷ contract33 ∷ contract34 ∷
  contract35 ∷ contract36 ∷ contract37 ∷ contract38 ∷ []

-- DASHI does not reinterpret a Lean theorem as global world truth. The
-- imported state remains a scoped evidence statement relative to the pinned
-- source snapshot and theorem proposition.
theoremReceiptState : Bool → Bool → EpistemicTrit
theoremReceiptState accepted sourceMatched with accepted | sourceMatched
... | true | true = supported
... | _ | _ = unresolved

sourceMismatchIsUnresolved : theoremReceiptState true false ≡ unresolved
sourceMismatchIsUnresolved = refl

acceptedSourceMatchedIsSupported : theoremReceiptState true true ≡ supported
acceptedSourceMatchedIsSupported = refl
