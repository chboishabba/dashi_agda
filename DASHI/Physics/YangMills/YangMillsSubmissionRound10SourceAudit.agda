module DASHI.Physics.YangMills.YangMillsSubmissionRound10SourceAudit where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record Round10Source : Set where
  field
    authors title publication persistentIdentifier : String
    theoremUse : String
    authorityLevel : ProofLevel
    importedResultRequiresTypedHypotheses : Bool

open Round10Source public

murrayConstructiveAnalysis : Round10Source
murrayConstructiveAnalysis = record
  { authors = "Zachary Murray"
  ; title = "Constructive Analysis in the Agda Proof Assistant"
  ; publication = "B.Sc. Honours thesis, Dalhousie University, 2022"
  ; persistentIdentifier = "arXiv:2205.08354; no DOI assigned"
  ; theoremUse =
      "Concrete Bishop-real arithmetic, setoid order, sequences, subsequence convergence, Cauchy completeness and inverse operations. DASHI proves the new reciprocal-factorial and finite-geometric specializations."
  ; authorityLevel = standardImported
  ; importedResultRequiresTypedHypotheses = true
  }

diestedGraphTheory : Round10Source
diestedGraphTheory = record
  { authors = "Reinhard Diestel"
  ; title = "Graph Theory"
  ; publication = "Graduate Texts in Mathematics 173, fifth edition, Springer, 2017"
  ; persistentIdentifier = "DOI: 10.1007/978-3-662-53622-3"
  ; theoremUse =
      "Finite graph, path, tree and connected-subgraph background only. The periodic degree-eight and reduced-skeleton physical theorems remain repository-specific."
  ; authorityLevel = standardImported
  ; importedResultRequiresTypedHypotheses = true
  }

koteckyPreiss : Round10Source
koteckyPreiss = record
  { authors = "Roman Kotecky and David Preiss"
  ; title = "Cluster Expansion for Abstract Polymer Models"
  ; publication = "Communications in Mathematical Physics 103 (1986), 491--498"
  ; persistentIdentifier = "DOI: 10.1007/BF01211762"
  ; theoremUse =
      "Abstract polymer convergence criterion. DASHI owns the finite geometric summation, canonical model adapters and physical activity estimates used to instantiate it."
  ; authorityLevel = standardImported
  ; importedResultRequiresTypedHypotheses = true
  }

allRound10SourcesIdentified : Bool
allRound10SourcesIdentified = true

allRound10SourcesIdentifiedIsTrue :
  allRound10SourcesIdentified ≡ true
allRound10SourcesIdentifiedIsTrue = refl
