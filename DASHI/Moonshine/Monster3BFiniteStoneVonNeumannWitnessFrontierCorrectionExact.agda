module DASHI.Moonshine.Monster3BFiniteStoneVonNeumannWitnessFrontierCorrectionExact where

------------------------------------------------------------------------
-- CORRECTED FINITE STONE--VON NEUMANN FRONTIER AFTER WITNESS EXTRACTION
--
-- Monster3BFiniteStoneVonNeumannFrontierExact was written before the finite
-- nonzero-coordinate search was constructed. Keep its leaf type and dependency
-- graph as the canonical historical owner; this thin correction updates the
-- states paid by constructive witness extraction and splits the
-- fixed-central-character uniqueness leaf at the proof-assistant boundary.
--
-- The constructive finite chain closes:
--
-- ordinary nonzero Schrodinger vector
--   -> selected nonzero X6 coordinate
--   -> norm-qualified cyclotomic amplitude
--   -> selected delta line
--   -> all translated delta lines
--   -> all Schrodinger functions.
--
-- The character-determination route is now sharpened too.  We consume
-- mathlib's scalar-product = equivariant-Hom-finrank theorem together with the
-- general simple-object Schur fact that a nonzero morphism between simples is
-- an isomorphism.  Equal characters identify the cross scalar product with the
-- self scalar product, whose Hom space is nonzero because it contains the
-- identity.  Therefore this implication does not require the stronger
-- algebraically-closed-field orthonormality shortcut.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Moonshine.Monster3BFiniteStoneVonNeumannFrontierExact as Frontier
import DASHI.Moonshine.Monster3BFiniteSchrodingerNonzeroWitnessExtractionExact as Witness
import DASHI.Wikimedia.IbrahimMonster3BMathlibCharacterDeterminationInteropExact as CharacterInterop

------------------------------------------------------------------------
-- 1. Same leaf carrier, corrected states only where actual proof exists.
------------------------------------------------------------------------

correctedLeafState : Frontier.StoneVonNeumannProofLeaf → Frontier.LeafState
correctedLeafState Frontier.constructCentralExtensionCarrier = Frontier.closed
correctedLeafState Frontier.proveFiniteHeisenbergGroupLaws = Frontier.closed
correctedLeafState Frontier.proveGlobalCommutatorNondegeneracy = Frontier.closed
correctedLeafState Frontier.constructSchrodingerFunctionModule = Frontier.closed
correctedLeafState Frontier.deriveModulationPointProjectors = Frontier.closed
correctedLeafState Frontier.proveProjector729AndOffPointSemantics = Frontier.closed
correctedLeafState Frontier.constructNonzeroCyclotomicInverse = Frontier.closed
correctedLeafState Frontier.extractDeltaLineFromNonzeroInvariantSubspace = Frontier.closed
correctedLeafState Frontier.proveTranslationOrbitReachesEveryDeltaLine = Frontier.closed
correctedLeafState Frontier.proveDeltaBasisSpansCarrier = Frontier.closed
correctedLeafState Frontier.proveTranslatedDeltaOrbitSpansCarrier = Frontier.closed
correctedLeafState Frontier.proveWitnessedIrreducibility = Frontier.closed
correctedLeafState Frontier.extractNonzeroCoordinateFromNonzeroVector = Frontier.closed
correctedLeafState Frontier.proveSchrodingerIrreducible = Frontier.closed
correctedLeafState Frontier.proveFixedCentralCharacterUniqueness = Frontier.open
correctedLeafState Frontier.identifyCertifiedMonster729Constituent = Frontier.blocked

nonzeroCoordinateLeafClosed :
  correctedLeafState Frontier.extractNonzeroCoordinateFromNonzeroVector
  ≡ Frontier.closed
nonzeroCoordinateLeafClosed = refl

schrodingerIrreducibilityLeafClosed :
  correctedLeafState Frontier.proveSchrodingerIrreducible
  ≡ Frontier.closed
schrodingerIrreducibilityLeafClosed = refl

------------------------------------------------------------------------
-- 2. The structural leaf is now split internally:
--
-- lower-level character/Hom theorem components  PAID upstream in mathlib
-- chosen route avoids algebraic closure          PAID by theorem inspection
-- concrete Lean equal-character/simple receipt  OPEN
-- concrete DASHI <-> mathlib representation map OPEN
-- resulting actual same-character isomorphism   BLOCKED on those transports.
------------------------------------------------------------------------

highestImpactStructuralLeafAfterWitness : Frontier.StoneVonNeumannProofLeaf
highestImpactStructuralLeafAfterWitness =
  Frontier.proveFixedCentralCharacterUniqueness

highestImpactStructuralLeafAfterWitnessIsOpen :
  correctedLeafState highestImpactStructuralLeafAfterWitness ≡ Frontier.open
highestImpactStructuralLeafAfterWitnessIsOpen = refl

certifiedMonster729IdentificationStillBlocked :
  correctedLeafState Frontier.identifyCertifiedMonster729Constituent
  ≡ Frontier.blocked
certifiedMonster729IdentificationStillBlocked = refl

characterInteropFrontier :
  CharacterInterop.MathlibCharacterDeterminationInteropFrontier
characterInteropFrontier =
  CharacterInterop.currentMathlibCharacterDeterminationInteropFrontier

------------------------------------------------------------------------
-- 3. Proof-bearing theorem snapshots.
------------------------------------------------------------------------

ordinaryNonzeroInvariantSubspaceIsWholeCarrier =
  Witness.ordinaryNonzeroInvariantSubspaceIsWholeCarrier

------------------------------------------------------------------------
-- 4. WrongType / non-promotion firewalls.
------------------------------------------------------------------------

data IrreducibilityCreatesUniqueness : Set where
data UpstreamTheoremCreatesDashiTransport : Set where
data AvoidingAlgebraicClosureCreatesLeanReceipt : Set where
data UniquenessCreatesMonsterIdentification : Set where
data Dimension729CreatesSameRepresentation : Set where
data CharacterDegreeCreatesIntertwiner : Set where
data QidCreatesFrontierClosure : Set where
data DeweyCreatesFrontierClosure : Set where
data OeisCreatesFrontierClosure : Set where

irreducibilityDoesNotCreateUniqueness : IrreducibilityCreatesUniqueness → ⊥
irreducibilityDoesNotCreateUniqueness ()

upstreamTheoremDoesNotCreateDashiTransport :
  UpstreamTheoremCreatesDashiTransport → ⊥
upstreamTheoremDoesNotCreateDashiTransport ()

avoidingAlgebraicClosureDoesNotCreateLeanReceipt :
  AvoidingAlgebraicClosureCreatesLeanReceipt → ⊥
avoidingAlgebraicClosureDoesNotCreateLeanReceipt ()

uniquenessDoesNotCreateMonsterIdentification :
  UniquenessCreatesMonsterIdentification → ⊥
uniquenessDoesNotCreateMonsterIdentification ()

dimension729DoesNotCreateSameRepresentation :
  Dimension729CreatesSameRepresentation → ⊥
dimension729DoesNotCreateSameRepresentation ()

characterDegreeDoesNotCreateIntertwiner : CharacterDegreeCreatesIntertwiner → ⊥
characterDegreeDoesNotCreateIntertwiner ()

qidDoesNotCreateFrontierClosure : QidCreatesFrontierClosure → ⊥
qidDoesNotCreateFrontierClosure ()

deweyDoesNotCreateFrontierClosure : DeweyCreatesFrontierClosure → ⊥
deweyDoesNotCreateFrontierClosure ()

oeisDoesNotCreateFrontierClosure : OeisCreatesFrontierClosure → ⊥
oeisDoesNotCreateFrontierClosure ()

------------------------------------------------------------------------
-- 5. External coordinates remain navigation/provenance only.
------------------------------------------------------------------------

record WitnessFrontierExternalCoordinates : Set where
  constructor witness-frontier-external-coordinates
  field
    finiteGroupQid : String
    groupRepresentationQid : String
    finiteGroupDewey : String
    groupRepresentationDewey : String
    oeisCoordinate : String
    oeisHasFrontierAuthority : Bool
open WitnessFrontierExternalCoordinates public

canonicalWitnessFrontierExternalCoordinates : WitnessFrontierExternalCoordinates
canonicalWitnessFrontierExternalCoordinates =
  witness-frontier-external-coordinates
    "Q1057968"
    "Q1055807"
    "512.23"
    "512.22"
    "A005052 remains numerical provenance for 90 = 10*3^2 only; it has no irreducibility, uniqueness, proof-transport, same-representation, Monster-identification, action, or intertwiner authority"
    false

------------------------------------------------------------------------
-- 6. Corrected frontier snapshot.
------------------------------------------------------------------------

record CorrectedStoneVonNeumannFrontier : Set where
  constructor corrected-stone-von-neumann-frontier
  field
    ordinaryNonzeroCoordinateExtractionPaid : Bool
    normQualifiedAmplitudeUpgradePaid : Bool
    finiteSchrodingerIrreducibilityPaid : Bool
    standardCharacterDeterminationTheoremPaid : Bool
    chosenCharacterRouteAvoidsAlgebraicClosure : Bool
    leanEqualCharacterSimpleIsoReceiptPaid : Bool
    dashiCharacterDeterminationTransportPaid : Bool
    fixedCentralCharacterUniquenessPaid : Bool
    certifiedMonster729ConstituentIdentificationPaid : Bool
    nextResidual : String
open CorrectedStoneVonNeumannFrontier public

currentCorrectedStoneVonNeumannFrontier : CorrectedStoneVonNeumannFrontier
currentCorrectedStoneVonNeumannFrontier =
  corrected-stone-von-neumann-frontier
    true true true
    true true false false
    false false
    "produce CharacterInterop.LeanEqualCharacterSimpleIsoReceipt over the existing exact Q(zeta_3) scalar field, then instantiate DashiToMathlibCharacterDeterminationTransport for the concrete extraspecial 3^(1+12) Schrodinger representation. The proof route is: character equality -> equal scalar products -> self Hom has positive finrank because identity is nonzero -> cross Hom has positive finrank -> nonzero equivariant morphism -> simple-object Schur isomorphism. No algebraic-closure scalar extension is required for this implication. After the Lean receipt and concrete FDRep/class-character bridge are paid, close fixed-central-character uniqueness and only then identify the certified Monster 729-dimensional constituent with the X6 Schrodinger model. Degree 729, character multiplicity, DOI/QID/Dewey/OEIS coordinates, and upstream theorem names do not create the Lean receipt, representation transport, or intertwiner."
