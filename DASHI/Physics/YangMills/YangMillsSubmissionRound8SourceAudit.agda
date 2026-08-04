module DASHI.Physics.YangMills.YangMillsSubmissionRound8SourceAudit where

------------------------------------------------------------------------
-- Round-eight source audit.
--
-- Primary sources are recorded with exact author/title/identifier metadata.
-- The recent 2602.0070 and 2602.0072 materials were supplied only through an
-- AI/vixra location.  Their bibliographic authority was not independently
-- established, so no author, title or DOI is invented and they cannot inhabit
-- a theorem field.  They serve only as architecture/audit leads.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import DASHI.Core.Prelude using (_×_; _,_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record Round8SourceEntry : Set where
  field
    authors : String
    title : String
    publication : String
    locator : String
    persistentIdentifier : String
    proofLevel : ProofLevel
    mayInhabitImportedTheorem : Bool

murrayConstructiveAnalysis : Round8SourceEntry
murrayConstructiveAnalysis = record
  { authors = "Zachary Murray"
  ; title = "Constructive Analysis in the Agda Proof Assistant"
  ; publication = "B.Sc. Honours thesis, Dalhousie University, 2022"
  ; locator = "constructive real completion, sequences and convergence"
  ; persistentIdentifier = "arXiv:2205.08354; no DOI assigned"
  ; proofLevel = standardImported
  ; mayInhabitImportedTheorem = true
  }

diestelGraphTheory : Round8SourceEntry
diestelGraphTheory = record
  { authors = "Reinhard Diestel"
  ; title = "Graph Theory"
  ; publication = "Graduate Texts in Mathematics 173, 5th edition, Springer, 2017"
  ; locator = "finite connected graphs, spanning trees, paths and distance"
  ; persistentIdentifier = "DOI:10.1007/978-3-662-53622-3"
  ; proofLevel = standardImported
  ; mayInhabitImportedTheorem = true
  }

balabanLargeFieldII : Round8SourceEntry
balabanLargeFieldII = record
  { authors = "Tadeusz Bałaban"
  ; title = "Large Field Renormalization II: Localization, Exponentiation, and Bounds for the R-Operation"
  ; publication = "Communications in Mathematical Physics 122 (1989), 355--392"
  ; locator = "polymer localization, exponentiation and R-operation bounds"
  ; persistentIdentifier = "DOI:10.1007/BF01238433"
  ; proofLevel = standardImported
  ; mayInhabitImportedTheorem = true
  }

koteckyPreiss : Round8SourceEntry
koteckyPreiss = record
  { authors = "Roman Kotecký and David Preiss"
  ; title = "Cluster Expansion for Abstract Polymer Models"
  ; publication = "Communications in Mathematical Physics 103 (1986), 491--498"
  ; locator = "abstract polymer convergence criterion"
  ; persistentIdentifier = "DOI:10.1007/BF01211762"
  ; proofLevel = standardImported
  ; mayInhabitImportedTheorem = true
  }

recent26020070AuditLead : Round8SourceEntry
recent26020070AuditLead = record
  { authors = "unverified"
  ; title = "unverified"
  ; publication = "user-supplied AI/vixra audit lead"
  ; locator = "identifier 2602.0070"
  ; persistentIdentifier = "no authoritative DOI recorded"
  ; proofLevel = conjectural
  ; mayInhabitImportedTheorem = false
  }

recent26020072AuditLead : Round8SourceEntry
recent26020072AuditLead = record
  { authors = "unverified"
  ; title = "unverified"
  ; publication = "user-supplied AI/vixra audit lead"
  ; locator = "identifier 2602.0072"
  ; persistentIdentifier = "no authoritative DOI recorded"
  ; proofLevel = conjectural
  ; mayInhabitImportedTheorem = false
  }

recentAuditLeadsCannotInhabit :
  (Round8SourceEntry.mayInhabitImportedTheorem recent26020070AuditLead
    ≡ false)
  ×
  (Round8SourceEntry.mayInhabitImportedTheorem recent26020072AuditLead
    ≡ false)
recentAuditLeadsCannotInhabit = refl , refl

round8SourceAuditLevel : ProofLevel
round8SourceAuditLevel = machineChecked
