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
-- The first half is now source-written in dashi_lean4:
--
--   cast_finrank_hom_left_eq_one_of_character_eq_add
--   cast_finrank_hom_right_eq_one_of_character_eq_add
--   cast_finrank_hom_other_eq_zero_of_character_eq_add
--
-- with a separate regression consumer on the normal Synthesis build path.
-- No Lean Action / kernel receipt has yet been observed for that head.
--
-- The remaining generic theorem is the semisimple assembly:
-- multiplicities 1,1,0 -> exactly two isotypic blocks -> direct sum.
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

leanMultiplicityDonorPath : String
leanMultiplicityDonorPath = "Synthesis/MonsterCharacterDetermination.lean"

leanMultiplicityRegressionPath : String
leanMultiplicityRegressionPath = "Synthesis/MonsterCharacterMultiplicityRegression.lean"

leanMultiplicityDonorHead : String
leanMultiplicityDonorHead = "751d58de09bcb37d1b1f3dbac2511f6cb362da5e"

------------------------------------------------------------------------
-- Exact cross-prover contract.
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
-- Classification/navigation coordinates remain non-promoting.
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
-- WrongType / non-promotion boundaries.
------------------------------------------------------------------------

data CharacterEqualityCreatesDirectSumWithoutSemisimplicity : Set where
data SourceApiExistsCreatesLeanTheorem : Set where
data LeanSourceCreatesLeanKernelReceipt : Set where
data LeanTheoremCreatesAgdaKernelProof : Set where
data GenericIsotypicCompilerCreatesMonsterSameAction : Set where
data DdcCreatesRepresentationDecomposition : Set where
data OeisCreatesRepresentationDecomposition : Set where

characterEqualityAloneDoesNotCreateDirectSum : CharacterEqualityCreatesDirectSumWithoutSemisimplicity → ⊥
characterEqualityAloneDoesNotCreateDirectSum ()

sourceApiDoesNotCreateLeanTheorem : SourceApiExistsCreatesLeanTheorem → ⊥
sourceApiDoesNotCreateLeanTheorem ()

leanSourceDoesNotCreateKernelReceipt : LeanSourceCreatesLeanKernelReceipt → ⊥
leanSourceDoesNotCreateKernelReceipt ()

leanTheoremDoesNotCreateAgdaKernelProof : LeanTheoremCreatesAgdaKernelProof → ⊥
leanTheoremDoesNotCreateAgdaKernelProof ()

genericCompilerDoesNotCreateMonsterSameAction : GenericIsotypicCompilerCreatesMonsterSameAction → ⊥
genericCompilerDoesNotCreateMonsterSameAction ()

ddcDoesNotCreateDecomposition : DdcCreatesRepresentationDecomposition → ⊥
ddcDoesNotCreateDecomposition ()

oeisDoesNotCreateDecomposition : OeisCreatesRepresentationDecomposition → ⊥
oeisDoesNotCreateDecomposition ()

------------------------------------------------------------------------
-- Highest-alpha cut.
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
    multiplicityRegressionSourceWritten : Bool
    multiplicityLemmasSourceWritten : Bool
    multiplicityLemmasLeanKernelChecked : Bool
    isotypicAssemblySourceWritten : Bool
    isotypicAssemblyLeanKernelChecked : Bool
    fullTwoSimpleCompilerTransportedToAgda : Bool
    actualMonsterFin90SameActionAttachmentPaid : Bool
    nextResidual : String
open TwoIsotypicCompilerFrontier public

currentTwoIsotypicCompilerFrontier : TwoIsotypicCompilerFrontier
currentTwoIsotypicCompilerFrontier = two-isotypic-compiler-frontier
  true true true true true true true
  true true false
  false false false false
  "the generic character-to-multiplicity half is now source-written in dashi_lean4 and its regression consumer is on the default Synthesis build path, but no Lean Action run is attached to head 751d58de09bcb37d1b1f3dbac2511f6cb362da5e. Do not promote it to kernel-paid. The next generic source leaf is only the semisimple assembly from multiplicities 1,1,0 to the two isotypic blocks and a direct-sum equivariant isomorphism, using pinned mathlib v4.28.0 Maschke/isotypic APIs. After an actual Lean kernel receipt, transport the result contract into Agda. The Monster-specific final leaf remains the SAME W_zeta action/intertwiner with X6 x Fin90; generic decomposition cannot create that same-object action weld."

phaseFrontier : Phase.PhaseCharacterWeldFrontier
phaseFrontier = Phase.currentPhaseCharacterWeldFrontier

characterProducerFrontier : CharacterProducer.MathlibCharacterDeterminationFrontier
characterProducerFrontier = CharacterProducer.currentMathlibCharacterDeterminationFrontier
