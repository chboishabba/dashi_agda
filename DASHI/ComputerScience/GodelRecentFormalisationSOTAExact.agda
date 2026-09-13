module DASHI.ComputerScience.GodelRecentFormalisationSOTAExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- RECENT GODEL / INCOMPLETENESS FORMALISATION SOTA (2026)
--
-- External formalisation/source status is a producer coordinate.  It does not
-- silently inhabit DASHI's local arithmetic ABI.  The useful question is
-- whether an external result pays the current diagonal consumer directly,
-- through a typed adapter, or only as prior art / source authority.
------------------------------------------------------------------------

coquandGodelII2026 : Source.AttributedSource
coquandGodelII2026 =
  Source.mkDOISource
    "Thierry Coquand"
    "Auto formalisation of Goedel's Second Incompleteness Theorem in Binary Recursive Arithmetic"
    "arXiv:2606.01898"
    "2026"
    "10.48550/arXiv.2606.01898"
    "https://arxiv.org/abs/2606.01898"
    Source.academicArticleSource
    "reports a postulate-free Agda formalisation of Goedel II for Church/Guard Basic Recursive Arithmetic; external theorem status does not instantiate DASHI's ArithmetisedFormalSystem"
    Source.publicAttribution

coquandChaitin2026 : Source.AttributedSource
coquandChaitin2026 =
  Source.mkDOISource
    "Thierry Coquand"
    "Auto formalisation of Chaitin and of the surprise incompleteness Theorem"
    "arXiv:2606.12462"
    "2026"
    "10.48550/arXiv.2606.12462"
    "https://arxiv.org/abs/2606.12462"
    Source.academicArticleSource
    "reports machine-checked Chaitin-Goedel I and Kritchman-Raz surprise-Goedel II developments over the same Basic Recursive Arithmetic framework; not a theorem import"
    Source.publicAttribution

coquandAgdaTree : Source.AttributedSource
coquandAgdaTree =
  Source.mkNoDOISource
    "Thierry Coquand"
    "agda-godel-tree"
    "GitHub repository"
    "2026"
    "https://github.com/coquand/agda-godel-tree"
    (Source.namedSourceKind "machine-checked source repository")
    "live Agda source carrier exposing Goedel I, Goedel II, Loeb, Chaitin and surprise-incompleteness modules for Basic Recursive Arithmetic; exact source paths remain external until same-object adapted"
    Source.publicAttribution

formalizedFormalLogicFoundation : Source.AttributedSource
formalizedFormalLogicFoundation =
  Source.mkNoDOISource
    "Formalized Formal Logic contributors"
    "Foundation"
    "Lean 4 package / GitHub repository"
    "2026"
    "https://github.com/FormalizedFormalLogic/Foundation"
    (Source.namedSourceKind "machine-checked Lean library")
    "live Lean 4 formal-logic library covering first/second incompleteness and provability logic including Solovay arithmetic completeness; external theorem declarations require exact adapter before paying DASHI consumers"
    Source.publicAttribution

vestrucciDiagonal2026 : Source.AttributedSource
vestrucciDiagonal2026 =
  Source.mkDOISource
    "Andrea Vestrucci"
    "Diagonalization as computation: Goedel sentence construction and a type-disciplined blueprint"
    "Archive for Mathematical Logic"
    "2026"
    "10.1007/s00153-026-01021-7"
    "https://doi.org/10.1007/s00153-026-01021-7"
    Source.academicArticleSource
    "explicit primitive-recursive code-transformer decomposition of Goedel diagonalisation; mechanism-level prior art and source alignment for DASHI's typed diagonal pipeline, not a machine proof import"
    Source.publicAttribution

vestrucciCorrection2026 : Source.AttributedSource
vestrucciCorrection2026 =
  Source.mkDOISource
    "Andrea Vestrucci"
    "Correction: Diagonalization as computation: Goedel sentence construction and a type-disciplined blueprint"
    "Archive for Mathematical Logic"
    "2026"
    "10.1007/s00153-026-01024-4"
    "https://doi.org/10.1007/s00153-026-01024-4"
    Source.academicArticleSource
    "correction carrier for the 2026 diagonalisation article; retained separately so corrected notation is not silently projected away"
    Source.publicAttribution

recentGodelSOTAAtlas : Source.AttributedSourceAtlas
recentGodelSOTAAtlas =
  Source.mkSourceAtlas
    "recent Goedel/incompleteness formalisation SOTA"
    "DASHI.ComputerScience.GodelRecentFormalisationSOTAExact"
    (coquandGodelII2026 ∷
     coquandChaitin2026 ∷
     coquandAgdaTree ∷
     formalizedFormalLogicFoundation ∷
     vestrucciDiagonal2026 ∷
     vestrucciCorrection2026 ∷ [])
    "2026 source and machine-formalisation carriers directly adjacent to the DASHI diagonal/provability seam"

------------------------------------------------------------------------
-- CONSUMER-RELATIVE ROLE
------------------------------------------------------------------------

data ExternalProducerRole : Set where
  machineCheckedSourceProducer
  theoremLibraryProducer
  mechanismAlignmentProducer : ExternalProducerRole

data LocalPaymentStatus : Set where
  externalOnly
  adapterRequired
  sameObjectPaymentAvailable : LocalPaymentStatus

data DiagonalCoordinate : Set where
  syntaxCoding
  substitutionPrimitiveRecursiveness
  internalRepresentability
  representedFunctionPrecomposition
  diagonalFixedPoint
  proofPredicate
  derivabilityConditions
  incompletenessResult : DiagonalCoordinate

record SOTAProducerReceipt : Set where
  constructor sotaProducerReceipt
  field
    source : Source.AttributedSource
    role : ExternalProducerRole
    relevantCoordinates : List DiagonalCoordinate
    paymentStatus : LocalPaymentStatus
    exactLocalAdapterOwned : Bool
    importsLocalProof : Bool

coquandProducer : SOTAProducerReceipt
coquandProducer =
  sotaProducerReceipt
    coquandAgdaTree
    machineCheckedSourceProducer
    (syntaxCoding ∷ substitutionPrimitiveRecursiveness ∷ internalRepresentability ∷
     diagonalFixedPoint ∷ proofPredicate ∷ derivabilityConditions ∷ incompletenessResult ∷ [])
    adapterRequired
    false
    false

foundationProducer : SOTAProducerReceipt
foundationProducer =
  sotaProducerReceipt
    formalizedFormalLogicFoundation
    theoremLibraryProducer
    (internalRepresentability ∷ diagonalFixedPoint ∷ proofPredicate ∷
     derivabilityConditions ∷ incompletenessResult ∷ [])
    adapterRequired
    false
    false

vestrucciProducer : SOTAProducerReceipt
vestrucciProducer =
  sotaProducerReceipt
    vestrucciDiagonal2026
    mechanismAlignmentProducer
    (syntaxCoding ∷ substitutionPrimitiveRecursiveness ∷ internalRepresentability ∷
     representedFunctionPrecomposition ∷ diagonalFixedPoint ∷ [])
    externalOnly
    false
    false

------------------------------------------------------------------------
-- CURRENT SOTA CUT
--
-- Vestrucci materially supports the exact decomposition we are using, but the
-- paper itself identifies mechanisation of that explicit pipeline as future
-- work.  Coquand and Foundation are machine-checked producers, but over their
-- own arithmetic/code/provability carriers.  Therefore none of the three can
-- be projected directly to a DASHI theorem inhabitant without a same-object
-- adapter.
------------------------------------------------------------------------

record RecentGodelSOTACut : Set where
  constructor recentGodelSOTACut
  field
    recentMachineCheckedGodelIIExists : Bool
    recentMachineCheckedChaitinRouteExists : Bool
    leanFoundationIncompletenessLibraryExists : Bool
    typedComputationalDiagonalBlueprintExists : Bool
    vestrucciPipelineMechanisedByThatPaper : Bool
    externalCarrierEqualsDASHICarrier : Bool
    currentShortestRouteIsAdapterSearch : Bool

canonicalRecentGodelSOTACut : RecentGodelSOTACut
canonicalRecentGodelSOTACut =
  recentGodelSOTACut true true true true false false true

------------------------------------------------------------------------
-- WRONGTYPE FIREWALLS
------------------------------------------------------------------------

data ExternalKernelProofImpliesLocalKernelProof : Set where
data SameTheoremNameImpliesSameFormalSystem : Set where
data ComputationalBlueprintImpliesFormalisation : Set where
data BasicRecursiveArithmeticEqualsDASHIArithmetic : Set where

externalKernelDoesNotImportLocalKernel :
  ExternalKernelProofImpliesLocalKernelProof → ⊥
externalKernelDoesNotImportLocalKernel ()

sameNameDoesNotIdentifyFormalSystems :
  SameTheoremNameImpliesSameFormalSystem → ⊥
sameNameDoesNotIdentifyFormalSystems ()

blueprintDoesNotCreateMachineProof :
  ComputationalBlueprintImpliesFormalisation → ⊥
blueprintDoesNotCreateMachineProof ()

braDoesNotDefinitionallyEqualDASHI :
  BasicRecursiveArithmeticEqualsDASHIArithmetic → ⊥
braDoesNotDefinitionallyEqualDASHI ()
