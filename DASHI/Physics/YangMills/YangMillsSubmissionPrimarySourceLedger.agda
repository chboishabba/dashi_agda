module DASHI.Physics.YangMills.YangMillsSubmissionPrimarySourceLedger where

open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Bibliographic identities used by the round-seven submission cutset.
-- Metadata is not a proof witness; it records the exact authority boundary
-- attached to the mathematical interfaces in the neighbouring modules.
------------------------------------------------------------------------

record SourceCitation : Set where
  field
    authors : String
    title : String
    publication : String
    locator : String
    persistentIdentifier : String

murrayConstructiveAnalysis : SourceCitation
murrayConstructiveAnalysis = record
  { authors = "Zachary Murray"
  ; title = "Constructive Analysis in the Agda Proof Assistant"
  ; publication = "B.Sc. Honours thesis, Dalhousie University, 2022"
  ; locator = "constructive reals, order, Cauchy completeness, and sequences"
  ; persistentIdentifier = "arXiv:2205.08354; no DOI assigned"
  }

diestelGraphTheory : SourceCitation
diestelGraphTheory = record
  { authors = "Reinhard Diestel"
  ; title = "Graph Theory"
  ; publication = "Graduate Texts in Mathematics 173, 5th edition, Springer, 2017"
  ; locator = "finite connected graphs, spanning trees, paths, and distance"
  ; persistentIdentifier = "DOI:10.1007/978-3-662-53622-3"
  }

balabanCMP109 : SourceCitation
balabanCMP109 = record
  { authors = "Tadeusz Bałaban"
  ; title = "Renormalization Group Approach to Lattice Gauge Field Theories. I"
  ; publication = "Communications in Mathematical Physics 109 (1987)"
  ; locator = "small-field averaging, contour comparison, and asymptotic-freedom input"
  ; persistentIdentifier = "DOI:10.1007/BF01215223"
  }

balabanGaugeFixingCMP99 : SourceCitation
balabanGaugeFixingCMP99 = record
  { authors = "Tadeusz Bałaban"
  ; title = "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge Fixing Conditions"
  ; publication = "Communications in Mathematical Physics 99 (1985)"
  ; locator = "regular configurations, background gauge, and gauge fixing"
  ; persistentIdentifier = "DOI:10.1007/BF01466594"
  }

balabanROperationI : SourceCitation
balabanROperationI = record
  { authors = "Tadeusz Bałaban"
  ; title = "Large Field Renormalization I: The Basic Step of the R-Operation"
  ; publication = "Communications in Mathematical Physics 122 (1989)"
  ; locator = "basic R-operation step"
  ; persistentIdentifier = "DOI:10.1007/BF01257412"
  }

balabanROperationII : SourceCitation
balabanROperationII = record
  { authors = "Tadeusz Bałaban"
  ; title = "Large Field Renormalization II: Localization, Exponentiation, and Bounds for the R-Operation"
  ; publication = "Communications in Mathematical Physics 122 (1989)"
  ; locator = "localization, exponentiation, and R-operation bounds"
  ; persistentIdentifier = "DOI:10.1007/BF01238433"
  }

koteckyPreissAbstractPolymers : SourceCitation
koteckyPreissAbstractPolymers = record
  { authors = "Roman Kotecký and David Preiss"
  ; title = "Cluster Expansion for Abstract Polymer Models"
  ; publication = "Communications in Mathematical Physics 103 (1986)"
  ; locator = "abstract polymer convergence criterion"
  ; persistentIdentifier = "DOI:10.1007/BF01211762"
  }

submissionPrimarySourceLedgerLevel : ProofLevel
submissionPrimarySourceLedgerLevel = machineChecked
