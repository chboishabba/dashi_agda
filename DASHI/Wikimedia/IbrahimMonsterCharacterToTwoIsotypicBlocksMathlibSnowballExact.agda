module DASHI.Wikimedia.IbrahimMonsterCharacterToTwoIsotypicBlocksMathlibSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.IbrahimMonster3BPhaseResolvedCharacterTwelveSeventyEightWeldExact as Phase
import DASHI.Wikimedia.IbrahimMonsterCharacterDeterminationMathlibProducerSnowballExact as CharacterProducer

------------------------------------------------------------------------
-- CHARACTER -> TWO ISOTYPIC BLOCKS: MINIMAL MATHLIB PRODUCER LEAF
--
-- The Monster-specific source work now pays, at character-family level,
--
--   chi(S_zeta) = chi_12 + chi_78,
--
-- with the two factors irreducible/non-isomorphic and total dimension 90.
-- What the existing Agda same-action consumer needs next is stronger than this:
-- two actual invariant blocks whose direct sum is the multiplicity carrier.
--
-- mathlib v4.28.0 already owns the standard generic ingredients:
--
--   * FDRep.scalar_product_char_eq_finrank_equivariant
--       character inner product = dimension of equivariant Hom;
--   * FDRep.char_orthonormal
--       orthogonality for simple finite-group representations;
--   * Maschke: IsSemisimpleModule k[G] V;
--   * isotypicComponent / isotypicComponents;
--   * sSupIndep_isotypicComponents;
--   * sSup_isotypicComponents = top.
--
-- Therefore the next cross-prover theorem is NOT a new Monster hypothesis and
-- not a general character-table engine.  It is a small assembly theorem:
--
--   if T,S are non-isomorphic simples,
--      char(V)=char(T)+char(S),
--      dim(V)=dim(T)+dim(S),
--   then V has exactly the T- and S-isotypic blocks, each multiplicity one,
--   those blocks are disjoint, and they exhaust V.
--
-- This owner records the producer contract and pinned APIs.  It does NOT claim
-- that the theorem has yet been source-written or Lean-kernel checked.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Source-code producer attribution, kept distinct by file/author role.
------------------------------------------------------------------------

mathlibCharacterSource : Attribution.AttributedSource
mathlibCharacterSource = Attribution.mkNoDOISource
  "Antoine Labelle; mathlib contributors"
  "Mathlib.RepresentationTheory.Character"
  "mathlib4 source, RequestProject pin v4.28.0"
  "pinned execution dependency"
  "https://github.com/leanprover-community/mathlib4/blob/v4.28.0/Mathlib/RepresentationTheory/Character.lean"
  (Attribution.namedSourceKind "machine-checked theorem producer source")
  "owns FDRep.char_orthonormal and FDRep.scalar_product_char_eq_finrank_equivariant; no DOI asserted for the source-code artifact"
  Attribution.publicAttribution

mathlibMaschkeSource : Attribution.AttributedSource
mathlibMaschkeSource = Attribution.mkNoDOISource
  "Kim Morrison; mathlib contributors"
  "Mathlib.RepresentationTheory.Maschke"
  "mathlib4 source, RequestProject pin v4.28.0"
  "pinned execution dependency"
  "https://github.com/leanprover-community/mathlib4/blob/v4.28.0/Mathlib/RepresentationTheory/Maschke.lean"
  (Attribution.namedSourceKind "machine-checked theorem producer source")
  "owns the finite-group IsSemisimpleModule instance under the nonmodular field hypothesis; no DOI asserted"
  Attribution.publicAttribution

mathlibIsotypicSource : Attribution.AttributedSource
mathlibIsotypicSource = Attribution.mkNoDOISource
  "Junyan Xu; mathlib contributors"
  "Mathlib.RingTheory.SimpleModule.Isotypic"
  "mathlib4 source, RequestProject pin v4.28.0"
  "pinned execution dependency"
  "https://github.com/leanprover-community/mathlib4/blob/v4.28.0/Mathlib/RingTheory/SimpleModule/Isotypic.lean"
  (Attribution.namedSourceKind "machine-checked theorem producer source")
  "owns isotypicComponent(s), sSup independence and exhaustion by isotypic components; no DOI asserted"
  Attribution.publicAttribution

characterAttribution = Snowball.canonicalSourceRoleSnowballReceipt mathlibCharacterSource
maschkeAttribution = Snowball.canonicalSourceRoleSnowballReceipt mathlibMaschkeSource
isotypicAttribution = Snowball.canonicalSourceRoleSnowballReceipt mathlibIsotypicSource

mathlibExecutionVersion : String
mathlibExecutionVersion = "v4.28.0"

------------------------------------------------------------------------
-- 2. Exact cross-prover contract.
------------------------------------------------------------------------

record TwoSimpleCharacterDecompositionProducer : Set₁ where
  field
    GroupCarrier : Set
    FieldCarrier : Set
    V T S : Set

    finiteGroup : Set
    algebraicallyClosedField : Set
    groupOrderInvertible : Set
    tSimple : Set
    sSimple : Set
    tAndSNonisomorphic : Set

    characterOfVIsCharacterTPlusCharacterS : Set
    dimensionOfVIsDimensionTPlusDimensionS : Set

    tEquivariantHomMultiplicityIsOne : Set
    sEquivariantHomMultiplicityIsOne : Set
    everyOtherSimpleHomMultiplicityIsZero : Set

    tIsotypicBlock : Set
    sIsotypicBlock : Set
    blocksDisjoint : Set
    blocksExhaustV : Set
    directSumEquivariantIsomorphism : Set

open TwoSimpleCharacterDecompositionProducer public

------------------------------------------------------------------------
-- 3. External classification coordinates remain navigation only.
------------------------------------------------------------------------

record IsotypicCompilerExternalCoordinates : Set where
  constructor isotypic-compiler-external-coordinates
  field
    groupRepresentationQid : String
    representationCharacterQid : String
    groupRepresentationDewey : String
    exactMathlibTheoremQid : String
    oeisCoordinate : String
    oeisHasCompilerAuthority : Bool
open IsotypicCompilerExternalCoordinates public

canonicalIsotypicCompilerExternalCoordinates : IsotypicCompilerExternalCoordinates
canonicalIsotypicCompilerExternalCoordinates = isotypic-compiler-external-coordinates
  "Q1055807"
  "Q600043"
  "512.22"
  "unresolved/not applicable: source-code theorem objects are pinned by repository version and theorem name, not assigned a guessed Wikidata QID"
  "not applicable: isotypic decomposition is representation theory, not integer-sequence evidence"
  false

------------------------------------------------------------------------
-- 4. WrongType / non-promotion boundaries.
------------------------------------------------------------------------

data CharacterEqualityCreatesDirectSumWithoutSemisimplicity : Set where
data SourceApiExistsCreatesLeanTheorem : Set where
data LeanTheoremCreatesAgdaKernelProof : Set where
data GenericIsotypicCompilerCreatesMonsterSameAction : Set where
data DdcCreatesRepresentationDecomposition : Set where
data OeisCreatesRepresentationDecomposition : Set where

characterEqualityAloneDoesNotCreateDirectSum :
  CharacterEqualityCreatesDirectSumWithoutSemisimplicity → ⊥
characterEqualityAloneDoesNotCreateDirectSum ()

sourceApiDoesNotCreateLeanTheorem : SourceApiExistsCreatesLeanTheorem → ⊥
sourceApiDoesNotCreateLeanTheorem ()

leanTheoremDoesNotCreateAgdaKernelProof : LeanTheoremCreatesAgdaKernelProof → ⊥
leanTheoremDoesNotCreateAgdaKernelProof ()

genericCompilerDoesNotCreateMonsterSameAction :
  GenericIsotypicCompilerCreatesMonsterSameAction → ⊥
genericCompilerDoesNotCreateMonsterSameAction ()

ddcDoesNotCreateDecomposition : DdcCreatesRepresentationDecomposition → ⊥
ddcDoesNotCreateDecomposition ()

oeisDoesNotCreateDecomposition : OeisCreatesRepresentationDecomposition → ⊥
oeisDoesNotCreateDecomposition ()

------------------------------------------------------------------------
-- 5. Highest-alpha cut.
------------------------------------------------------------------------

record TwoIsotypicCompilerFrontier : Set where
  constructor two-isotypic-compiler-frontier
  field
    pinnedCharacterInnerProductAPI : Bool
    pinnedIrreducibleOrthogonalityAPI : Bool
    pinnedMaschkeSemisimplicityAPI : Bool
    pinnedIsotypicComponentAPI : Bool
    pinnedIsotypicIndependenceAPI : Bool
    pinnedIsotypicExhaustionAPI : Bool
    monsterPhaseCharacterTwelvePlusSeventyEightPaid : Bool
    genericTwoSimpleCompilerSourceWritten : Bool
    genericTwoSimpleCompilerLeanKernelChecked : Bool
    genericTwoSimpleCompilerTransportedToAgda : Bool
    actualMonsterFin90SameActionAttachmentPaid : Bool
    nextResidual : String
open TwoIsotypicCompilerFrontier public

currentTwoIsotypicCompilerFrontier : TwoIsotypicCompilerFrontier
currentTwoIsotypicCompilerFrontier = two-isotypic-compiler-frontier
  true true true true true true true
  false false false false
  "implement the generic two-simple character decomposition in the existing dashi_lean4 Synthesis lane against mathlib v4.28.0. First derive equivariant-Hom multiplicities 1,1,0 from FDRep.scalar_product_char_eq_finrank_equivariant plus char_orthonormal; then use the pinned semisimple/isotypic-component API to obtain disjoint T/S blocks exhausting V. Keep this theorem generic. After a Lean kernel receipt, transport only its result contract into Agda and apply it to the source-paid 12/78 multiplicity character. The Monster-specific remaining leaf is still the SAME actual W_zeta -> X6 x Fin90 action/intertwiner; a generic direct-sum compiler cannot manufacture that same-action weld."

phaseFrontier : Phase.PhaseCharacterWeldFrontier
phaseFrontier = Phase.currentPhaseCharacterWeldFrontier

characterProducerFrontier : CharacterProducer.MathlibCharacterDeterminationFrontier
characterProducerFrontier = CharacterProducer.currentMathlibCharacterDeterminationFrontier
