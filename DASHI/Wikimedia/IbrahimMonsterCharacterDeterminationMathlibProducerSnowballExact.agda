module DASHI.Wikimedia.IbrahimMonsterCharacterDeterminationMathlibProducerSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Moonshine.Monster3BFiniteStoneVonNeumannUniquenessBidiExact as Uniqueness
import DASHI.Wikimedia.IbrahimMonsterCharacterDeterminationPrimarySourceSnowballExact as Serre

------------------------------------------------------------------------
-- MATHLIB CHARACTER-DETERMINATION PRODUCER SNOWBALL
--
-- The generic Monster 3B uniqueness frontier no longer needs to be treated as
-- an undifferentiated request to re-prove characteristic-zero character
-- theory.  Current mathlib owns the machine-checked orthogonality theorem
--
--   Representation.char_orthonormal
--
-- (and the FDRep version) for irreducible finite-group representations over an
-- algebraically closed field with |G| invertible in the coefficient field.
--
-- This theorem is strong enough to make the desired corollary tiny:
-- equal irreducible characters force Nonempty (Equiv sigma rho), because the
-- common character inner product is 1, whereas the no-isomorphism branch of
-- char_orthonormal is 0.
--
-- Important ownership split:
--   Serre 1977              = mathematical literature provenance;
--   mathlib Character.lean  = external machine-checked producer;
--   a tiny Lean corollary    = still needs an execution receipt;
--   Agda IrreducibleCharacterDetermination = local consumer interface;
--   same-object actual W_zeta attachment    = separate downstream payment.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Exact external code-source pin.
------------------------------------------------------------------------

mathlibCharacterSource : Attribution.AttributedSource
mathlibCharacterSource = Attribution.mkNoDOISource
  "Antoine Labelle; leanprover-community/mathlib contributors"
  "Mathlib.RepresentationTheory.Character"
  "mathlib4 source repository"
  "pinned 2026-09-11 investigation snapshot"
  "https://github.com/leanprover-community/mathlib4/blob/63ed4eba5d2be3bb2e99bc7158e07f08cd9189ec/Mathlib/RepresentationTheory/Character.lean"
  (Attribution.namedSourceKind "machine-checked theorem-library source")
  "external Lean theorem producer for finite-group character orthogonality; no DOI asserted for the code artifact and no Agda proof imported by citation"
  Attribution.publicAttribution

mathlibCharacterAttribution =
  Snowball.canonicalSourceRoleSnowballReceipt mathlibCharacterSource

record MathlibCharacterSourcePin : Set where
  constructor mathlib-character-source-pin
  field
    repository : String
    branchSnapshotCommit : String
    latestCharacterFileTouchCommit : String
    sourcePath : String
    sourceAuthorHeader : String
    representationTheorem : String
    fdRepTheorem : String
    sourceDOI : String
    sourceDOIResolved : Bool
open MathlibCharacterSourcePin public

canonicalMathlibCharacterSourcePin : MathlibCharacterSourcePin
canonicalMathlibCharacterSourcePin = mathlib-character-source-pin
  "leanprover-community/mathlib4"
  "63ed4eba5d2be3bb2e99bc7158e07f08cd9189ec"
  "950d27063f377d5ccd80d3eeedcebe319d3eb821"
  "Mathlib/RepresentationTheory/Character.lean"
  "Antoine Labelle"
  "Representation.char_orthonormal"
  "FDRep.char_orthonormal"
  "unresolved / not asserted for mathlib source file"
  false

------------------------------------------------------------------------
-- 2. Mathematical provenance remains Serre, not silently transferred to the
--    code author.  Reuse the existing attributed source rather than duplicate
--    a second bibliographic object.
------------------------------------------------------------------------

serreMathematicalSource : Attribution.AttributedSource
serreMathematicalSource = Serre.serreCharacterSource

serreMathematicalAttribution =
  Snowball.canonicalSourceRoleSnowballReceipt serreMathematicalSource

serreDOI : String
serreDOI = "10.1007/978-1-4684-9458-7"

------------------------------------------------------------------------
-- 3. QID / Dewey / OEIS coordinates.  These are discovery and classification
--    coordinates only.  Topic Dewey values are not promoted to a claim about
--    the catalogue classification of Serre's particular book.
------------------------------------------------------------------------

record CharacterDeterminationExternalCoordinates : Set where
  constructor character-determination-external-coordinates
  field
    groupRepresentationQid : String
    representationCharacterQid : String
    finiteGroupQid : String
    maschkeTheoremQid : String
    groupRepresentationDewey : String
    finiteGroupDewey : String
    serreBookDewey : String
    serreBookDeweyResolved : Bool
    relevantOEIS : String
    oeisHasTheoremAuthorityHere : Bool
open CharacterDeterminationExternalCoordinates public

canonicalCharacterDeterminationExternalCoordinates :
  CharacterDeterminationExternalCoordinates
canonicalCharacterDeterminationExternalCoordinates =
  character-determination-external-coordinates
    "Q1055807"
    "Q600043"
    "Q1057968"
    "Q656198"
    "512.22"
    "512.23"
    "unresolved"
    false
    "not applicable: this theorem is representation-theoretic, not an integer-sequence identity"
    false

------------------------------------------------------------------------
-- 4. Exact producer theorem shape extracted from mathlib.
------------------------------------------------------------------------

record MathlibCharOrthonormalProducer : Set where
  constructor mathlib-char-orthonormal-producer
  field
    finiteGroupRequired : Bool
    fieldRequired : Bool
    finiteDimensionalRequired : Bool
    groupOrderInvertibleRequired : Bool
    algebraicallyClosedRequired : Bool
    leftIrreducibleRequired : Bool
    rightIrreducibleRequired : Bool
    characterInnerProductComputed : Bool
    isomorphismExistenceAppearsInConclusion : Bool
    theoremMachineCheckedInMathlib : Bool
open MathlibCharOrthonormalProducer public

canonicalMathlibCharOrthonormalProducer : MathlibCharOrthonormalProducer
canonicalMathlibCharOrthonormalProducer = mathlib-char-orthonormal-producer
  true true true true true true true true true true

------------------------------------------------------------------------
-- 5. The desired corollary is now a *tiny cross-prover wrapper*, not a request
--    for a new representation theory library.  We deliberately do not mark it
--    paid until an actual Lean execution receipt exists.
------------------------------------------------------------------------

record EqualCharacterIsoCorollaryRoute : Set where
  constructor equal-character-iso-corollary-route
  field
    sourceTheoremName : String
    desiredConclusion : String
    proofIdea : String
    requiresNewMaschkeProof : Bool
    requiresNewSchurProof : Bool
    requiresCharacterTableEnumeration : Bool
    leanWrapperSourceWritten : Bool
    leanKernelReceiptObserved : Bool
    agdaTransportReceiptObserved : Bool
open EqualCharacterIsoCorollaryRoute public

currentEqualCharacterIsoCorollaryRoute : EqualCharacterIsoCorollaryRoute
currentEqualCharacterIsoCorollaryRoute = equal-character-iso-corollary-route
  "Representation.char_orthonormal / FDRep.char_orthonormal"
  "equal irreducible characters -> Nonempty equivariant isomorphism"
  "rewrite the two orthogonality inner products using character equality; the self-pair is 1, while the no-isomorphism branch is 0; contradiction with one_ne_zero eliminates the empty-isomorphism branch"
  false false false
  false false false

------------------------------------------------------------------------
-- 6. Local consumer alignment.  The existing Agda record remains authoritative
--    for downstream use; this file does not pretend a theorem-name citation is
--    an inhabitant of that record.
------------------------------------------------------------------------

localConsumer : Set₂
localConsumer = Uniqueness.IrreducibleCharacterDetermination

record MathlibToDASHICharacterDeterminationTransport : Set₂ where
  field
    theory : Uniqueness.IrreducibleCharacterDetermination
    sourcePinMatchesProducer : Set
    leanWrapperKernelReceipt : Set
    theoremStatementSameObject : Set
    crossProverTransportReceipt : Set
open MathlibToDASHICharacterDeterminationTransport public

------------------------------------------------------------------------
-- 7. WrongType / attribution boundaries.
------------------------------------------------------------------------

data MathlibTheoremNameCreatesAgdaWitness : Set where
data SerreCitationCreatesLeanKernelReceipt : Set where
data TopicDeweyClassifiesSpecificBook : Set where
data QidCreatesEquivariantIso : Set where
data OeisCreatesCharacterTheorem : Set where
\data ExternalOrthogonalityAutomaticallyAttachesActualMonsterSector : Set where

mathlibNameDoesNotCreateAgdaWitness : MathlibTheoremNameCreatesAgdaWitness → ⊥
mathlibNameDoesNotCreateAgdaWitness ()

serreCitationDoesNotCreateLeanReceipt : SerreCitationCreatesLeanKernelReceipt → ⊥
serreCitationDoesNotCreateLeanReceipt ()

topicDeweyDoesNotClassifySpecificBook : TopicDeweyClassifiesSpecificBook → ⊥
topicDeweyDoesNotClassifySpecificBook ()

qidDoesNotCreateIso : QidCreatesEquivariantIso → ⊥
qidDoesNotCreateIso ()

oeisDoesNotCreateCharacterTheorem : OeisCreatesCharacterTheorem → ⊥
oeisDoesNotCreateCharacterTheorem ()

orthogonalityDoesNotAttachActualMonsterSector :
  ExternalOrthogonalityAutomaticallyAttachesActualMonsterSector → ⊥
orthogonalityDoesNotAttachActualMonsterSector ()

------------------------------------------------------------------------
-- 8. Highest-alpha frontier after the source search.
------------------------------------------------------------------------

record MathlibCharacterDeterminationSnowballFrontier : Set where
  constructor mathlib-character-determination-snowball-frontier
  field
    serrePrimaryMathematicalSourcePaid : Bool
    serreDOIPaid : Bool
    mathlibMachineProducerLocated : Bool
    mathlibSourceCommitPinned : Bool
    mathlibTheoremNamesPinned : Bool
    representationQidsPaid : Bool
    topicDeweyCoordinatesPaid : Bool
    bookSpecificDeweyPaid : Bool
    oeisCorrectlyMarkedNonAuthoritative : Bool
    orthogonalityTheoremMachineCheckedExternally : Bool
    equalCharacterLeanCorollaryKernelPaid : Bool
    agdaCrossProverTransportPaid : Bool
    actualMonsterSameObjectAttachmentPaid : Bool
    nextResidual : String
open MathlibCharacterDeterminationSnowballFrontier public

currentMathlibCharacterDeterminationSnowballFrontier :
  MathlibCharacterDeterminationSnowballFrontier
currentMathlibCharacterDeterminationSnowballFrontier =
  mathlib-character-determination-snowball-frontier
    true true true true true true true false true true
    false false false
    "write the smallest Lean wrapper over the pinned mathlib char_orthonormal theorem proving equal irreducible characters imply Nonempty equivariant isomorphism; obtain a Lean kernel receipt and content-address that exact source/result. Then transport only that theorem into the existing Agda IrreducibleCharacterDetermination interface. Do not re-prove Maschke/Schur in Agda, and do not attach the result to W_zeta until the actual restricted Monster representation is same-object connected."
