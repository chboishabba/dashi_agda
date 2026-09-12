module DASHI.Moonshine.Monster3BFiniteStoneVonNeumannWitnessFrontierCorrectionExact where

------------------------------------------------------------------------
-- CORRECTED FINITE STONE--VON NEUMANN FRONTIER AFTER WITNESS EXTRACTION
--
-- Monster3BFiniteStoneVonNeumannFrontierExact was written before the finite
-- nonzero-coordinate search was constructed.  Keep its leaf type and
-- dependency graph as the canonical historical owner; this thin correction
-- updates only the states paid by
-- Monster3BFiniteSchrodingerNonzeroWitnessExtractionExact.
--
-- The constructive chain now closes:
--
-- ordinary nonzero Schrodinger vector
--   -> selected nonzero X6 coordinate
--   -> norm-qualified cyclotomic amplitude
--   -> selected delta line
--   -> all translated delta lines
--   -> all Schrodinger functions.
--
-- This proves irreducibility of the concrete finite Schrodinger model in the
-- repository's invariant-subspace sense.  It does NOT prove the finite
-- Stone--von Neumann uniqueness theorem, and it does NOT identify any actual
-- Monster 729-dimensional constituent with this model.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Moonshine.Monster3BFiniteStoneVonNeumannFrontierExact as Frontier
import DASHI.Moonshine.Monster3BFiniteSchrodingerNonzeroWitnessExtractionExact as Witness

------------------------------------------------------------------------
-- 1. Same leaf carrier, corrected states only where new proof exists.
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
-- 2. The next high-alpha structural leaf is now uniqueness for the fixed
--    nontrivial central character.
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

------------------------------------------------------------------------
-- 3. Proof-bearing theorem snapshot, reusing the actual new theorem rather
--    than a Boolean promotion.
------------------------------------------------------------------------

ordinaryNonzeroInvariantSubspaceIsWholeCarrier =
  Witness.ordinaryNonzeroInvariantSubspaceIsWholeCarrier

------------------------------------------------------------------------
-- 4. WrongType / non-promotion firewalls.
------------------------------------------------------------------------

data IrreducibilityCreatesUniqueness : Set where
data UniquenessCreatesMonsterIdentification : Set where
data Dimension729CreatesSameRepresentation : Set where
data CharacterDegreeCreatesIntertwiner : Set where
data QidCreatesFrontierClosure : Set where
data DeweyCreatesFrontierClosure : Set where
data OeisCreatesFrontierClosure : Set where

irreducibilityDoesNotCreateUniqueness : IrreducibilityCreatesUniqueness → ⊥
irreducibilityDoesNotCreateUniqueness ()

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
    "A005052 remains numerical provenance for 90 = 10*3^2 only; it has no irreducibility, uniqueness, same-representation, Monster-identification, action, or intertwiner authority"
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
    fixedCentralCharacterUniquenessPaid : Bool
    certifiedMonster729ConstituentIdentificationPaid : Bool
    nextResidual : String
open CorrectedStoneVonNeumannFrontier public

currentCorrectedStoneVonNeumannFrontier : CorrectedStoneVonNeumannFrontier
currentCorrectedStoneVonNeumannFrontier =
  corrected-stone-von-neumann-frontier
    true true true false false
    "prove finite Stone-von Neumann uniqueness for irreducible representations of the constructed extraspecial Heisenberg group with the fixed nontrivial central character. Only after that theorem is proof-bearing may the certified 729-dimensional Monster-kernel constituent be identified with the X6 Schrodinger model through an explicit same-central-character representation isomorphism. Degree 729, character multiplicity, DOI/QID/Dewey/OEIS coordinates, or abstract uniqueness slogans do not create that identification."
