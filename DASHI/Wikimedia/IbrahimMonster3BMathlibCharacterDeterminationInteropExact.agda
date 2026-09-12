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

------------------------------------------------------------------------
-- MATHLIB CHARACTER-DETERMINATION INTEROP
--
-- The corrected highest-alpha route does not need to pass through an
-- algebraically closed scalar extension.  Mathlib's lower-level theorem
--
--   FDRep.scalar_product_char_eq_finrank_equivariant
--
-- already identifies the character scalar product with the finrank of the
-- equivariant-Hom space over any field where the finite group order is
-- invertible.  For simple representations with equal characters:
--
--   cross Hom finrank = self Hom finrank > 0,
--
-- because the self Hom contains the nonzero identity.  Hence there is a
-- nonzero equivariant morphism.  General Schur simplicity then makes that
-- morphism an isomorphism; this nonzero-simple-morphism step does not require
-- algebraic closure.  Algebraic closure is used by char_orthonormal only for
-- the stronger normalization End(V) has finrank exactly 1.
--
-- This owner therefore records the weaker theorem route actually consumed by
-- DASHI and keeps the earlier scalar-extension owners as independent valid
-- constructions rather than prerequisites for character determination.
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
  "standard representation-theory authority for character determination and Schur theory; not a repository proof-transport receipt"
  Attribution.publicAttribution

serreAttribution = Snowball.canonicalSourceRoleSnowballReceipt serre

------------------------------------------------------------------------
-- 2. Exact machine-checked upstream manifestations.
------------------------------------------------------------------------

record MathlibCharacterDeterminationCoordinate : Set where
  constructor mathlib-character-determination-coordinate
  field
    repository : String
    characterSourceFile : String
    characterSourceBlobSha : String
    schurSourceFile : String
    schurSourceBlobSha : String
    scalarProductTheorem : String
    nonIsoSimpleHomZeroTheorem : String
    finiteGroupRequired : Bool
    algebraicallyClosedFieldRequiredForChosenRoute : Bool
    groupOrderInvertibleInFieldRequired : Bool
    simpleRepresentationsRequired : Bool
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
    "Mathlib/CategoryTheory/Preadditive/Schur.lean"
    "0a9d695f4f24c0f9fad00116cfa4c840451dd3de"
    "FDRep.scalar_product_char_eq_finrank_equivariant"
    "finrank_hom_simple_simple_eq_zero_of_not_iso"
    true false true true true false

algebraicClosureIsNotRequiredForChosenRoute : Bool
algebraicClosureIsNotRequiredForChosenRoute = true

------------------------------------------------------------------------
-- 3. Lean-side receipt for the weaker equal-character -> isomorphism route.
--
-- We do not manufacture the Lean proof from theorem names.  A real Lean
-- producer must discharge these steps for the concrete FDRep carrier over the
-- exact DASHI cyclotomic field and return the transported isomorphism theorem.
------------------------------------------------------------------------

record LeanEqualCharacterSimpleIsoReceipt : Set₁ where
  field
    scalarProductEqualsEquivariantHomFinrank : Set
    equalCharactersIdentifyCrossAndSelfScalarProducts : Set
    selfIdentityMorphismIsNonzero : Set
    selfEquivariantHomFinrankPositive : Set
    equalCharactersForceNonzeroEquivariantHom : Set
    nonzeroSimpleMorphismIsIso : Set
    algebraicClosureNotUsed : Set
    leanProofArtifact : Set
open LeanEqualCharacterSimpleIsoReceipt public

------------------------------------------------------------------------
-- 4. Cross-kernel transport consumed by the existing Stone-von Neumann owner.
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

    -- Concrete proof receipt over the original exact scalar field.  No
    -- Cyclotomic3ScalarExtension is a prerequisite for this route.
    leanEqualCharacterSimpleIsoReceipt : LeanEqualCharacterSimpleIsoReceipt

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
-- 5. WrongType / non-promotion firewalls.
------------------------------------------------------------------------

data MathlibTheoremCreatesDashiTransport : Set where
data OrthogonalityShortcutMakesAlgebraicClosureNecessary : Set where
data DOICharacterCitationCreatesTransport : Set where
data EqualCharacterValuesChooseBasis : Set where
data QidCreatesCharacterDetermination : Set where
data DeweyCreatesCharacterDetermination : Set where
data OeisCreatesCharacterDetermination : Set where

mathlibTheoremDoesNotCreateDashiTransport :
  MathlibTheoremCreatesDashiTransport → ⊥
mathlibTheoremDoesNotCreateDashiTransport ()

orthogonalityShortcutDoesNotMakeAlgebraicClosureNecessary :
  OrthogonalityShortcutMakesAlgebraicClosureNecessary → ⊥
orthogonalityShortcutDoesNotMakeAlgebraicClosureNecessary ()

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
-- 6. Navigation/provenance coordinates remain non-promoting.
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
    "A005052 remains numerical provenance for 90 = 10*3^2 only; it has no irreducibility, character scalar-product, Hom-space, Schur-isomorphism, representation-isomorphism, basis, or proof-transport authority"
    false

------------------------------------------------------------------------
-- 7. Pareto frontier.
------------------------------------------------------------------------

record MathlibCharacterDeterminationInteropFrontier : Set where
  constructor mathlib-character-determination-interop-frontier
  field
    standardMathematicalTheoremSourcePaid : Bool
    exactMathlibCharacterSourceManifestationPinned : Bool
    exactMathlibSchurSourceManifestationPinned : Bool
    scalarProductHomFinrankTheoremLocated : Bool
    simpleNonIsoHomZeroTheoremLocated : Bool
    chosenRouteAvoidsAlgebraicClosure : Bool
    upstreamKernelProofComponentsExist : Bool
    leanEqualCharacterSimpleIsoReceiptObserved : Bool
    dashiRepresentationTransportPaid : Bool
    agdaKernelReplayPaid : Bool
    fixedPhaseRepresentationIsoCompilerAvailable : Bool
    nextResidual : String
open MathlibCharacterDeterminationInteropFrontier public

currentMathlibCharacterDeterminationInteropFrontier :
  MathlibCharacterDeterminationInteropFrontier
currentMathlibCharacterDeterminationInteropFrontier =
  mathlib-character-determination-interop-frontier
    true true true true true true true
    false false false true
    "produce LeanEqualCharacterSimpleIsoReceipt over the existing exact Q(zeta_3) field: instantiate FDRep.scalar_product_char_eq_finrank_equivariant, rewrite the cross scalar product by concrete character equality to the self scalar product, use the nonzero identity to prove self Hom finrank positive, obtain a nonzero cross equivariant morphism, and use simple-object Schur to turn it into an isomorphism. Then package the concrete finite Heisenberg FDRep and prove its DASHI class-character equals the mathlib trace. The earlier algebraic-closure scalar-extension route remains a valid independent construction but is not a prerequisite for this character-determination implication. Serre DOI/QID/Dewey/OEIS coordinates and theorem names do not create the Lean receipt or representation transport."
