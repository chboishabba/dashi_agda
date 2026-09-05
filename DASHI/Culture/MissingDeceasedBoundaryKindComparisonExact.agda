module DASHI.Culture.MissingDeceasedBoundaryKindComparisonExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.KnowledgeBoundaryKindBidiExact as K

------------------------------------------------------------------------
-- CROSS-ROSTER BOUNDARY-KIND COMPARISON
--
-- This owner separates CLOSED same-object transitions from contextual boundary
-- adjacency. A restricted meeting followed by a public summary, or a public
-- accelerator paper inside a classified weapons programme, is not silently
-- promoted to declassification of the same knowledge object.
------------------------------------------------------------------------

data BoundaryClosureStatus : Set where
  closedSameObject
  documentedBoundaryNoCompletedSameObjectTransfer
  contextualBoundaryAdjacency
  unresolvedBoundary
  : BoundaryClosureStatus

record BoundaryKindCase : Set where
  constructor boundary-kind-case
  field
    personOrProgramme : String
    boundaryKind : K.BoundaryKind
    closureStatus : BoundaryClosureStatus
    sourceReference : String
    boundedReading : String

open BoundaryKindCase public

rezaPatentCase : BoundaryKindCase
rezaPatentCase = boundary-kind-case
  "Monica Jacinto / Dallis Hardwick patent application US09/954,835"
  K.ordinaryPatentConfidentiality
  closedSameObject
  "35 U.S.C. 122; USPTO MPEP 1120/1128; US20030053926A1"
  "The same USPTO application record moved from statutory confidentiality to public application publication. This is routine patent publication, not sensitive declassification."

poamsCase : BoundaryKindCase
poamsCase = boundary-kind-case
  "POAMS / Quantum Machines / NASA SAA8-1519855"
  K.contractualProprietaryBoundary
  documentedBoundaryNoCompletedSameObjectTransfer
  "NASA/TM-20205010911, especially Space Act proprietary-period and V5/data-custody discussion"
  "NASA documents a proprietary period and later public TM, while V5 hardware/data custody remained with Quantum Machines. The exact Amy 2020 reviewed object is unresolved and all underlying layers are not shown to have become public."

leblancFicsWorkshopCase : BoundaryKindCase
leblancFicsWorkshopCase = boundary-kind-case
  "NASA Fission Instrumentation & Controls workshop -> later FSP I&C public webinar reporting"
  K.internalInstitutionalBoundary
  contextualBoundaryAdjacency
  "NASA 2024 FICS Workshop page; NASA NTRS 20250008475"
  "The 2024 workshop required attendees to be U.S. persons and later public NTRS material reports workshop outcomes, including the live FICS database and technology-growth path. No exact same-artifact or same-dataset private->public weld is established."

chavezScorpiusCase : BoundaryKindCase
chavezScorpiusCase = boundary-kind-case
  "Anthony Chavez / DARHT-Scorpius public engineering surface within stockpile-stewardship programme"
  K.classifiedNationalSecurityBoundary
  contextualBoundaryAdjacency
  "DOE/NNSA public Scorpius/DARHT material; DOE DARHT EIS notes nuclear-weapons design details are classified"
  "Public sources expose accelerator architecture and programme purpose inside a national-security environment containing classified weapons-design information. No same-object classified->public transition attributable to Chavez is established."

loureiroViriatoCase : BoundaryKindCase
loureiroViriatoCase = boundary-kind-case
  "Nuno F. G. Loureiro / Viriato"
  K.unresolvedBoundaryKind
  unresolvedBoundary
  "Viriato CPC paper, arXiv preprint, MIT PSFC profile"
  "Model, algorithms, implementation architecture and benchmarks are public. This pass still does not locate a source-code release or a prior bounded state for the same code artifact."

record CurrentBoundaryKindComparison : Set where
  constructor current-boundary-kind-comparison
  field
    anyClosedBoundary : Bool
    anyClosedBoundaryIsTrue : anyClosedBoundary ≡ true
    routinePatentBoundaryClosed : Bool
    routinePatentBoundaryClosedIsTrue : routinePatentBoundaryClosed ≡ true
    nonRoutineSensitiveSameObjectBoundaryClosed : Bool
    nonRoutineSensitiveSameObjectBoundaryClosedIsFalse :
      nonRoutineSensitiveSameObjectBoundaryClosed ≡ false
    poamsContractualBoundaryDocumented : Bool
    poamsContractualBoundaryDocumentedIsTrue :
      poamsContractualBoundaryDocumented ≡ true
    leblancExactSameObjectBoundaryClosed : Bool
    leblancExactSameObjectBoundaryClosedIsFalse :
      leblancExactSameObjectBoundaryClosed ≡ false
    chavezExactDeclassificationBoundaryClosed : Bool
    chavezExactDeclassificationBoundaryClosedIsFalse :
      chavezExactDeclassificationBoundaryClosed ≡ false
    viriatoPriorBoundedArtifactLocated : Bool
    viriatoPriorBoundedArtifactLocatedIsFalse :
      viriatoPriorBoundedArtifactLocated ≡ false

canonicalCurrentBoundaryKindComparison : CurrentBoundaryKindComparison
canonicalCurrentBoundaryKindComparison = current-boundary-kind-comparison
  true refl
  true refl
  false refl
  true refl
  false refl
  false refl
  false refl
