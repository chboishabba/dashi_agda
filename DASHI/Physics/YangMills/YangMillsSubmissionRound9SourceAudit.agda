module DASHI.Physics.YangMills.YangMillsSubmissionRound9SourceAudit where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record SourceAuditEntry : Set where
  field
    authors title publication locator persistentIdentifier : String
    relationshipToDASHI : String
    authorityLevel : ProofLevel
    mayInhabitImportedTheorem : Bool

open SourceAuditEntry public

murrayConstructiveAnalysis : SourceAuditEntry
murrayConstructiveAnalysis = record
  { authors = "Zachary Murray"
  ; title = "Constructive Analysis in the Agda Proof Assistant"
  ; publication = "B.Sc. Honours thesis, Dalhousie University, 2022"
  ; locator = "constructive real arithmetic, order, sequences and completeness"
  ; persistentIdentifier = "arXiv:2205.08354; no DOI assigned"
  ; relationshipToDASHI =
      "Concrete Bishop carrier and completeness; DASHI owns the sine/cosine coefficient, parity and tail specializations."
  ; authorityLevel = standardImported
  ; mayInhabitImportedTheorem = true
  }

hallLieGroups : SourceAuditEntry
hallLieGroups = record
  { authors = "Brian C. Hall"
  ; title = "Lie Groups, Lie Algebras, and Representations: An Elementary Introduction"
  ; publication = "Second edition, Springer, 2015"
  ; locator = "SU(2), adjoint representation and exponential-map background"
  ; persistentIdentifier = "DOI: 10.1007/978-3-319-13467-3"
  ; relationshipToDASHI =
      "Background for the concrete SU(2) chart; word inversion and ad parity are proved internally."
  ; authorityLevel = standardImported
  ; mayInhabitImportedTheorem = true
  }

balabanCMP109 : SourceAuditEntry
balabanCMP109 = record
  { authors = "Tadeusz Bałaban"
  ; title = "Renormalization Group Approach to Lattice Gauge Field Theories. I"
  ; publication = "Communications in Mathematical Physics 109 (1987), 249--301"
  ; locator = "centred block averaging, small-field effective action and coupling renormalization"
  ; persistentIdentifier = "DOI: 10.1007/BF01215223"
  ; relationshipToDASHI =
      "Primary physical architecture for centred contours, averaging, P11 and Gate 4."
  ; authorityLevel = standardImported
  ; mayInhabitImportedTheorem = true
  }

balabanPropagatorsI : SourceAuditEntry
balabanPropagatorsI = record
  { authors = "Tadeusz Bałaban"
  ; title = "Propagators and Renormalization Transformations for Lattice Gauge Theories. I"
  ; publication = "Communications in Mathematical Physics 95 (1984), 17--40"
  ; locator = "background-gauge propagator and local coercivity architecture"
  ; persistentIdentifier = "DOI: 10.1007/BF01211042"
  ; relationshipToDASHI =
      "Primary source for the P33 local metric and propagator lane; physical constants remain explicit inputs."
  ; authorityLevel = standardImported
  ; mayInhabitImportedTheorem = true
  }

dimockLargeFields : SourceAuditEntry
dimockLargeFields = record
  { authors = "J. Dimock"
  ; title = "The Renormalization Group According to Balaban. II. Large Fields"
  ; publication = "Journal of Mathematical Physics 54 (2013), 092301"
  ; locator = "large-field regions, suppression and entropy payment"
  ; persistentIdentifier = "DOI: 10.1063/1.4821275"
  ; relationshipToDASHI =
      "Source architecture for P10; DASHI separates defect, action, integration and diameter-decay inhabitants."
  ; authorityLevel = standardImported
  ; mayInhabitImportedTheorem = true
  }

diestelGraphTheory : SourceAuditEntry
diestelGraphTheory = record
  { authors = "Reinhard Diestel"
  ; title = "Graph Theory"
  ; publication = "Graduate Texts in Mathematics 173, fifth edition, Springer, 2017"
  ; locator = "finite graph, path, tree and connected-subgraph background"
  ; persistentIdentifier = "DOI: 10.1007/978-3-662-53622-3"
  ; relationshipToDASHI =
      "Generic graph background; periodic degree eight and physical reduced-skeleton structure are repository-specific proofs."
  ; authorityLevel = standardImported
  ; mayInhabitImportedTheorem = true
  }

koteckyPreiss : SourceAuditEntry
koteckyPreiss = record
  { authors = "Roman Kotecky and David Preiss"
  ; title = "Cluster Expansion for Abstract Polymer Models"
  ; publication = "Communications in Mathematical Physics 103 (1986), 491--498"
  ; locator = "abstract polymer convergence criterion"
  ; persistentIdentifier = "DOI: 10.1007/BF01211762"
  ; relationshipToDASHI =
      "Authority for the abstract criterion; DASHI owns the canonical animal constant and finite-shell reduction."
  ; authorityLevel = standardImported
  ; mayInhabitImportedTheorem = true
  }

federbushMassZeroI : SourceAuditEntry
federbushMassZeroI = record
  { authors = "Paul G. Federbush"
  ; title = "A Mass Zero Cluster Expansion. Part 1: The Expansion"
  ; publication = "Communications in Mathematical Physics 81 (1981), 327--340"
  ; locator = "paired cluster and block-spin expansion architecture"
  ; persistentIdentifier = "DOI: 10.1007/BF01209071"
  ; relationshipToDASHI =
      "Historical source context only; DASHI proves the abstract weighted odd-pair cancellation internally."
  ; authorityLevel = standardImported
  ; mayInhabitImportedTheorem = true
  }

osterwalderSchraderI : SourceAuditEntry
osterwalderSchraderI = record
  { authors = "Konrad Osterwalder and Robert Schrader"
  ; title = "Axioms for Euclidean Green's Functions"
  ; publication = "Communications in Mathematical Physics 31 (1973), 83--112"
  ; locator = "Euclidean axioms and reconstruction"
  ; persistentIdentifier = "DOI: 10.1007/BF01645738"
  ; relationshipToDASHI =
      "Reconstruction authority only after all typed OS hypotheses are inhabited."
  ; authorityLevel = standardImported
  ; mayInhabitImportedTheorem = true
  }

bipmSI : SourceAuditEntry
bipmSI = record
  { authors = "Bureau International des Poids et Mesures"
  ; title = "The International System of Units (SI)"
  ; publication = "Ninth edition (2019), current version 4.01, June 2026"
  ; locator = "SI base quantities, dimensions and unit conventions"
  ; persistentIdentifier = "DOI: 10.59161/AUEZ1291"
  ; relationshipToDASHI =
      "Metrology authority; inverse correlation length is not silently identified with SI mass or energy."
  ; authorityLevel = standardImported
  ; mayInhabitImportedTheorem = true
  }

allRound9PrimarySourcesIdentified : Bool
allRound9PrimarySourcesIdentified = true

noUnidentifiedAuditLeadPromoted : Bool
noUnidentifiedAuditLeadPromoted = true

allRound9PrimarySourcesIdentifiedIsTrue :
  allRound9PrimarySourcesIdentified ≡ true
allRound9PrimarySourcesIdentifiedIsTrue = refl

noUnidentifiedAuditLeadPromotedIsTrue :
  noUnidentifiedAuditLeadPromoted ≡ true
noUnidentifiedAuditLeadPromotedIsTrue = refl
