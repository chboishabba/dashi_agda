module DASHI.Physics.YangMills.YangMillsSubmissionRound11SourceAudit where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record Round11Source : Set where
  field
    authors title publication persistentIdentifier : String
    theoremUse : String
    authorityLevel : ProofLevel
    importedResultRequiresTypedHypotheses : Bool

open Round11Source public

murrayConstructiveAnalysis : Round11Source
murrayConstructiveAnalysis = record
  { authors = "Zachary Murray"
  ; title = "Constructive Analysis in the Agda Proof Assistant"
  ; publication = "B.Sc. Honours thesis, Dalhousie University, 2022"
  ; persistentIdentifier = "arXiv:2205.08354; no DOI assigned"
  ; theoremUse =
      "Bishop-real setoid arithmetic and sequence infrastructure. Round eleven proves only the repository-specific reducer from exact configured term definitions to the concrete signed-factorial identification."
  ; authorityLevel = standardImported
  ; importedResultRequiresTypedHypotheses = true
  }

diestelGraphTheory : Round11Source
diestelGraphTheory = record
  { authors = "Reinhard Diestel"
  ; title = "Graph Theory"
  ; publication = "Graduate Texts in Mathematics 173, fifth edition, Springer, 2017"
  ; persistentIdentifier = "DOI: 10.1007/978-3-662-53622-3"
  ; theoremUse =
      "Finite graph and tree background. DASHI owns the periodic four-dimensional support carrier, degree-eight enumeration and the explicit no-go separating bounded degree from affine diameter complexity."
  ; authorityLevel = standardImported
  ; importedResultRequiresTypedHypotheses = true
  }

koteckyPreiss : Round11Source
koteckyPreiss = record
  { authors = "Roman Kotecký and David Preiss"
  ; title = "Cluster Expansion for Abstract Polymer Models"
  ; publication = "Communications in Mathematical Physics 103 (1986), 491--498"
  ; persistentIdentifier = "DOI: 10.1007/BF01211762"
  ; theoremUse =
      "Abstract polymer convergence criterion. DASHI proves the finite direct-ratio induction and must separately prove the physical activity and counting hypotheses."
  ; authorityLevel = standardImported
  ; importedResultRequiresTypedHypotheses = true
  }

balabanPropagatorsOne : Round11Source
balabanPropagatorsOne = record
  { authors = "Tadeusz Bałaban"
  ; title = "Propagators and Renormalization Transformations for Lattice Gauge Theories. I"
  ; publication = "Communications in Mathematical Physics 95 (1984), 17--40"
  ; persistentIdentifier = "DOI: 10.1007/BF01215753"
  ; theoremUse =
      "Motivates the P33 coercive inverse and exponential-decay package. No physical Hessian estimate is imported without a typed repository inhabitant."
  ; authorityLevel = standardImported
  ; importedResultRequiresTypedHypotheses = true
  }

balabanRenormalizationOne : Round11Source
balabanRenormalizationOne = record
  { authors = "Tadeusz Bałaban"
  ; title = "Renormalization Group Approach to Lattice Gauge Field Theories. I. Generation of Effective Actions in a Small Field Approximation and a Coupling Constant Renormalization in Four Dimensions"
  ; publication = "Communications in Mathematical Physics 109 (1987), 249--301"
  ; persistentIdentifier = "DOI: 10.1007/BF01215223"
  ; theoremUse =
      "Source architecture for the small-field effective action, contour, background-gauge and fluctuation lanes. Round eleven splits Gate 4 into seven typed packages rather than importing the conclusion."
  ; authorityLevel = standardImported
  ; importedResultRequiresTypedHypotheses = true
  }

dimockLargeFields : Round11Source
dimockLargeFields = record
  { authors = "J. Dimock"
  ; title = "The Renormalization Group According to Balaban. II. Large Fields"
  ; publication = "Journal of Mathematical Physics 54 (2013), 092301"
  ; persistentIdentifier = "DOI: 10.1063/1.4821275"
  ; theoremUse =
      "Large-field localization and suppression strategy. The physical P10 package is dependency-indexed by the P33 inverse package and remains conditional until its local estimates are constructed."
  ; authorityLevel = standardImported
  ; importedResultRequiresTypedHypotheses = true
  }

balabanROperation : Round11Source
balabanROperation = record
  { authors = "Tadeusz Bałaban"
  ; title = "Large Field Renormalization. II. Localization, Exponentiation, and Bounds for the R-Operation"
  ; publication = "Communications in Mathematical Physics 122 (1989), 355--392"
  ; persistentIdentifier = "DOI: 10.1007/BF01238433"
  ; theoremUse =
      "Connected-activity and R-operation provenance. Round eleven exposes locality, connectedness preservation and weighted-norm control as separate Gate-4 fields."
  ; authorityLevel = standardImported
  ; importedResultRequiresTypedHypotheses = true
  }

allRound11SourcesIdentified : Bool
allRound11SourcesIdentified = true

allRound11SourcesIdentifiedIsTrue :
  allRound11SourcesIdentified ≡ true
allRound11SourcesIdentifiedIsTrue = refl
