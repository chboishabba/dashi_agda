module DASHI.Wikimedia.IbrahimMonster3BMathlibCharacterDeterminationInteropExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Set₁; Set₂)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Moonshine.Monster3BKernelCharacterCriterionExact as Character
import DASHI.Moonshine.Monster3BFiniteStoneVonNeumannUniquenessBidiExact as Uniqueness
import DASHI.Wikimedia.IbrahimMonster3BCyclotomicScalarExtensionInteropExact as ScalarExtension

------------------------------------------------------------------------
-- MATHLIB CHARACTER-DETERMINATION INTEROP
--
-- The finite Stone--von Neumann BIDI owner has reduced the next open
-- mathematical leaf to the standard characteristic-zero theorem that two
-- irreducible finite-group representations with the same character are
-- equivariantly isomorphic.
--
-- Current mathlib source has a kernel-checked route through
--
--   FDRep.scalar_product_char_eq_finrank_equivariant
--   FDRep.char_orthonormal
--
-- in Mathlib/RepresentationTheory/Character.lean.  The concrete DASHI
-- Schrodinger representation, however, is over exact Q(zeta_3) amplitudes, not
-- yet an algebraically closed field.  Therefore the first transport payment is
-- the exact cyclotomic scalar-extension seam; only after that may a concrete
-- FDRep and class-character comparison be supplied.
--
-- Citation or theorem-name equality is not proof transport. No Lean proof is
-- claimed to have been replayed by the Agda kernel in this owner.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Mathematical source attribution.
------------------------------------------------------------------------

serre : Attribution.AttributedSource
serre = Attribution.mkDOISource
  "Jean-Pierre Serre"
  "Linear Representations of Finite Groups"
  "Springer"
  "1977"
  "10.1007/978-1-4684-9458-7"
  "https://doi.org/10.1007/978-1-4684-9458-7"
  Attribution.academicArticleSource
  "standard representation-theory authority for character determination and Schur orthogonality; not a repository proof-transport receipt"
  Attribution.publicAttribution

serreAttribution = Snowball.canonicalSourceRoleSnowballReceipt serre

------------------------------------------------------------------------
-- 2. Exact machine-checked upstream manifestation.
------------------------------------------------------------------------

record MathlibCharacterDeterminationCoordinate : Set where
  constructor mathlib-character-determination-coordinate
  field
    repository : String
    sourceFile : String
    sourceBlobSha : String
    scalarProductTheorem : String
    orthogonalityTheorem : String
    finiteGroupRequired : Bool
    algebraicallyClosedFieldRequired : Bool
    groupOrderInvertibleInFieldRequired : Bool
    irreducibleRepresentationsRequired : Bool
    upstreamKernelChecked : Bool
    replayedByAgdaKernelHere : Bool
open MathlibCharacterDeterminationCoordinate public

canonicalMathlibCharacterDeterminationCoordinate :
  MathlibCharacterDeterminationCoordinate
canonicalMathlibCharacterDeterminationCoordinate =
  mathlib-character-determination-coordinate
    "leanprover-community/mathlib4"
    "Mathlib/RepresentationTheory/Character.lean"
    "d131ae62882df478bb2aadf013181b4c5b31b328"
    "FDRep.scalar_product_char_eq_finrank_equivariant"
    "FDRep.char_orthonormal"
    true true true true true false

cyclotomicScalarExtensionFrontier :
  ScalarExtension.CyclotomicScalarExtensionFrontier
cyclotomicScalarExtensionFrontier =
  ScalarExtension.currentCyclotomicScalarExtensionFrontier

------------------------------------------------------------------------
-- 3. Only the cross-kernel transport is still an implementation obligation.
------------------------------------------------------------------------

record DashiToMathlibCharacterDeterminationTransport : Set₂ where
  field
    Representation : Set₁
    CharacterOf :
      Representation →
      Character.ExtraspecialClassKind →
      Character.CyclotomicTrace3
    IsIrreducible : Representation → Set
    EquivariantIso : Representation → Representation → Set

    -- Receipt that the exact scalar extension and DASHI representation objects
    -- satisfy the finite-group/field/simple-object hypotheses of the pinned
    -- mathlib theorem and that its resulting isomorphism has been transported
    -- back to this EquivariantIso carrier.
    scalarExtension : ScalarExtension.Cyclotomic3ScalarExtension
    schrodingerScalarExtension :
      ScalarExtension.SchrodingerScalarExtensionTransport scalarExtension

    transportedEqualCharactersGiveIso :
      (left right : Representation) →
      IsIrreducible left →
      IsIrreducible right →
      ((kind : Character.ExtraspecialClassKind) →
        CharacterOf left kind ≡ CharacterOf right kind) →
      EquivariantIso left right

open DashiToMathlibCharacterDeterminationTransport public

compileIrreducibleCharacterDetermination :
  DashiToMathlibCharacterDeterminationTransport →
  Uniqueness.IrreducibleCharacterDetermination
compileIrreducibleCharacterDetermination transport = record
  { Representation = Representation transport
  ; CharacterOf = CharacterOf transport
  ; IsIrreducible = IsIrreducible transport
  ; EquivariantIso = EquivariantIso transport
  ; equalCharactersGiveIso = transportedEqualCharactersGiveIso transport
  }

------------------------------------------------------------------------
-- 4. WrongType / non-promotion firewalls.
------------------------------------------------------------------------

data MathlibTheoremCreatesDashiTransport : Set where
data ScalarExtensionCreatesCharacterEquality : Set where
data DOICharacterCitationCreatesTransport : Set where
data EqualCharacterValuesChooseBasis : Set where
data QidCreatesCharacterDetermination : Set where
data DeweyCreatesCharacterDetermination : Set where
data OeisCreatesCharacterDetermination : Set where

mathlibTheoremDoesNotCreateDashiTransport :
  MathlibTheoremCreatesDashiTransport → ⊥
mathlibTheoremDoesNotCreateDashiTransport ()

scalarExtensionDoesNotCreateCharacterEquality :
  ScalarExtensionCreatesCharacterEquality → ⊥
scalarExtensionDoesNotCreateCharacterEquality ()

doiCitationDoesNotCreateTransport :
  DOICharacterCitationCreatesTransport → ⊥
doiCitationDoesNotCreateTransport ()

equalCharacterValuesDoNotChooseBasis : EqualCharacterValuesChooseBasis → ⊥
equalCharacterValuesDoNotChooseBasis ()

qidDoesNotCreateCharacterDetermination : QidCreatesCharacterDetermination → ⊥
qidDoesNotCreateCharacterDetermination ()

deweyDoesNotCreateCharacterDetermination : DeweyCreatesCharacterDetermination → ⊥
deweyDoesNotCreateCharacterDetermination ()

oeisDoesNotCreateCharacterDetermination : OeisCreatesCharacterDetermination → ⊥
oeisDoesNotCreateCharacterDetermination ()

------------------------------------------------------------------------
-- 5. Navigation/provenance coordinates remain non-promoting.
------------------------------------------------------------------------

record CharacterDeterminationExternalCoordinates : Set where
  constructor character-determination-external-coordinates
  field
    groupRepresentationQid : String
    representationCharacterQid : String
    finiteGroupQid : String
    groupRepresentationDewey : String
    finiteGroupDewey : String
    oeisCoordinate : String
    oeisHasCharacterDeterminationAuthority : Bool
open CharacterDeterminationExternalCoordinates public

canonicalCharacterDeterminationExternalCoordinates :
  CharacterDeterminationExternalCoordinates
canonicalCharacterDeterminationExternalCoordinates =
  character-determination-external-coordinates
    "Q1055807"
    "Q600043"
    "Q1057968"
    "512.22"
    "512.23"
    "A005052 remains numerical provenance for 90 = 10*3^2 only; it has no scalar-extension, irreducibility, character-orthogonality, representation-isomorphism, basis, or proof-transport authority"
    false

------------------------------------------------------------------------
-- 6. Pareto frontier.
------------------------------------------------------------------------

record MathlibCharacterDeterminationInteropFrontier : Set where
  constructor mathlib-character-determination-interop-frontier
  field
    standardMathematicalTheoremSourcePaid : Bool
    exactMathlibSourceManifestationPinned : Bool
    scalarProductTheoremLocated : Bool
    irreducibleOrthogonalityTheoremLocated : Bool
    upstreamKernelProofExists : Bool
    cyclotomicScalarExtensionInterfaceAvailable : Bool
    scalarExtensionPaid : Bool
    dashiRepresentationTransportPaid : Bool
    agdaKernelReplayPaid : Bool
    fixedPhaseRepresentationIsoCompilerAvailable : Bool
    nextResidual : String
open MathlibCharacterDeterminationInteropFrontier public

currentMathlibCharacterDeterminationInteropFrontier :
  MathlibCharacterDeterminationInteropFrontier
currentMathlibCharacterDeterminationInteropFrontier =
  mathlib-character-determination-interop-frontier
    true true true true true
    true false
    false false true
    "first instantiate Cyclotomic3ScalarExtension for the exact Q(zeta_3) amplitude algebra and SchrodingerScalarExtensionTransport for the existing X6 function module, preserving all six translation and six modulation actions. Then package that extended action as the finite-dimensional mathlib FDRep used by DashiToMathlibCharacterDeterminationTransport, prove the DASHI cyclotomic class-character agrees with its trace, and transport the resulting FDRep isomorphism back. Only then may the corrected Stone-von Neumann frontier mark fixed-central-character uniqueness closed. DOI/QID/Dewey/OEIS coordinates and upstream theorem existence do not create scalar extension, character equality, or proof transport."
