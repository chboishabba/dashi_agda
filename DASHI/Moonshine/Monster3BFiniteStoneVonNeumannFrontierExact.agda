module DASHI.Moonshine.Monster3BFiniteStoneVonNeumannFrontierExact where

------------------------------------------------------------------------
-- FINITE STONE-VON NEUMANN FRONTIER FOR THE MONSTER 3B HEISENBERG FACTOR
--
-- Structural prerequisites are theorem-bearing: finite group laws and global
-- commutator nondegeneracy are closed.  The concrete Q(zeta_3)[X6] function
-- model and modulation-derived point projectors extract one literal delta line
-- from every supplied nonzero invariant-vector witness.  Translation
-- transitivity then forces every delta line into that subspace, and the generic
-- ternary finite-function basis theorem reconstructs every Schrodinger
-- function from those point masses.
--
-- Therefore the old compound translated-delta spanning payment is closed.
-- What remains before unconditional irreducibility is the witness-interface
-- payment: an arbitrary mathematically nonzero invariant subspace/vector must
-- supply an actual point with nonzero cyclotomic amplitude.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)

import DASHI.Moonshine.Monster3BHeisenbergMultiplicityExact as Multiplicity
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as Generators
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as Central
import DASHI.Moonshine.Monster3BFiniteHeisenbergNondegeneracyExact as Nondegenerate
import DASHI.Moonshine.Monster3BFiniteHeisenbergGroupLawFrontierExact as GroupLaws
import DASHI.Moonshine.Monster3BElementaryAbelianInvariantExact as Elementary
import DASHI.Moonshine.Base369AppraisalFibreHeisenbergCarrierBidiExact as Fibre
import DASHI.Moonshine.Monster3BFiniteSchrodingerFunctionModuleExact as FunctionModule
import DASHI.Moonshine.Monster3BFiniteSchrodingerCoordinateProjectorExact as CoordinateProjector
import DASHI.Moonshine.Monster3BFiniteSchrodingerPointProjectorExact as PointProjector
import DASHI.Moonshine.Monster3BFiniteSchrodingerPointProjectorEvaluationExact as ProjectorEvaluation
import DASHI.Moonshine.Monster3BFiniteSchrodingerProjector729Exact as Projector729
import DASHI.Moonshine.Monster3BCyclotomicNonzeroInverseExact as CyclotomicInverse
import DASHI.Moonshine.Monster3BFiniteX6ConstructiveComparisonExact as X6Comparison
import DASHI.Moonshine.Monster3BFiniteSchrodingerDeltaExtractionExact as DeltaExtraction
import DASHI.Moonshine.Monster3BFiniteSchrodingerDeltaOrbitTransitivityExact as Orbit
import DASHI.Moonshine.TernaryFiniteFunctionDeltaBasisExact as Basis

centreOrder : Nat
centreOrder = Elementary.centreOrder

lagrangianDimension : Nat
lagrangianDimension = Elementary.lLagrangianDimension

symplecticQuotientDimension : Nat
symplecticQuotientDimension = Elementary.fullSymplecticDimension

schrodingerDegree : Nat
schrodingerDegree = Elementary.schrodingerDimension

centreOrderIsThree : centreOrder ≡ 3
centreOrderIsThree = refl

lagrangianDimensionIsSix : lagrangianDimension ≡ 6
lagrangianDimensionIsSix = refl

symplecticQuotientDimensionIsTwelve : symplecticQuotientDimension ≡ 12
symplecticQuotientDimensionIsTwelve = refl

schrodingerDegreeIs729 : schrodingerDegree ≡ 729
schrodingerDegreeIs729 = refl

extraspecialOrderIsThreePowerThirteen :
  Multiplicity.extraspecialOrder ≡ 1594323
extraspecialOrderIsThreePowerThirteen = Multiplicity.extraspecialOrderIs3Power13

nonlinearDegreeMatchesSchrodinger :
  Multiplicity.nonlinearCharacterDegree Multiplicity.plusType
  ≡ schrodingerDegree
nonlinearDegreeMatchesSchrodinger = refl

base369FibreMatchesSchrodingerDegree :
  Fibre.heisenbergFibreStateCount ≡ schrodingerDegree
base369FibreMatchesSchrodingerDegree = refl

finiteHeisenbergGroupLawsAvailable : Bool
finiteHeisenbergGroupLawsAvailable =
  GroupLaws.finiteHeisenbergGroupLawsComplete
    GroupLaws.canonicalHeisenbergGroupLawBoundary

finiteHeisenbergGroupLawsAvailableIsTrue :
  finiteHeisenbergGroupLawsAvailable ≡ true
finiteHeisenbergGroupLawsAvailableIsTrue = refl

constructiveGlobalNondegeneracyAvailable : Bool
constructiveGlobalNondegeneracyAvailable =
  Nondegenerate.globalSymplecticNondegeneracyProved
    Nondegenerate.canonicalHeisenbergNondegeneracyBoundary

constructiveGlobalNondegeneracyAvailableIsTrue :
  constructiveGlobalNondegeneracyAvailable ≡ true
constructiveGlobalNondegeneracyAvailableIsTrue = refl

functionModuleConstructed : Bool
functionModuleConstructed =
  FunctionModule.exactFunctionCarrierConstructed
    FunctionModule.canonicalSchrodingerFunctionModuleBoundary

coordinateProjectorsConstructed : Bool
coordinateProjectorsConstructed =
  CoordinateProjector.projectorDerivedFromModulationAction
    CoordinateProjector.canonicalCoordinateProjectorBoundary

pointProjectorConstructed : Bool
pointProjectorConstructed =
  PointProjector.sixCoordinateProjectorConstructed
    PointProjector.canonicalPointProjectorBoundary

projectorOffPointEvaluationConstructed : Bool
projectorOffPointEvaluationConstructed =
  ProjectorEvaluation.explicitOffPointVanishingProved
    ProjectorEvaluation.canonicalPointProjectorEvaluationBoundary

projectorScale729Constructed : Bool
projectorScale729Constructed =
  Projector729.sixCoordinateProjectorScaleIs729
    Projector729.canonicalProjector729Boundary

nonzeroCyclotomicInverseConstructed : Bool
nonzeroCyclotomicInverseConstructed =
  CyclotomicInverse.rightInverseProved
    CyclotomicInverse.canonicalCyclotomicInverseBoundary

constructiveX6ComparisonConstructed : Bool
constructiveX6ComparisonConstructed =
  X6Comparison.x6ComparisonReturnsEqualityOrDifferenceCoordinate
    X6Comparison.canonicalX6ComparisonBoundary

deltaLineExtractionConstructed : Bool
deltaLineExtractionConstructed =
  DeltaExtraction.invariantSubspaceContainsSelectedDeltaLine
    DeltaExtraction.canonicalDeltaExtractionBoundary

allDeltaOrbitLinesConstructed : Bool
allDeltaOrbitLinesConstructed =
  Orbit.all729DeltaLinesForcedIntoInvariantSubspace
    Orbit.canonicalDeltaOrbitTransitivityBoundary

deltaBasisSpanningConstructed : Bool
deltaBasisSpanningConstructed =
  Basis.all729DeltasSpanEverySchrodingerFunction
    Basis.canonicalTernaryFiniteFunctionDeltaBasisBoundary

functionModuleConstructedIsTrue : functionModuleConstructed ≡ true
functionModuleConstructedIsTrue = refl

coordinateProjectorsConstructedIsTrue : coordinateProjectorsConstructed ≡ true
coordinateProjectorsConstructedIsTrue = refl

pointProjectorConstructedIsTrue : pointProjectorConstructed ≡ true
pointProjectorConstructedIsTrue = refl

projectorOffPointEvaluationConstructedIsTrue :
  projectorOffPointEvaluationConstructed ≡ true
projectorOffPointEvaluationConstructedIsTrue = refl

projectorScale729ConstructedIsTrue : projectorScale729Constructed ≡ true
projectorScale729ConstructedIsTrue = refl

nonzeroCyclotomicInverseConstructedIsTrue :
  nonzeroCyclotomicInverseConstructed ≡ true
nonzeroCyclotomicInverseConstructedIsTrue = refl

constructiveX6ComparisonConstructedIsTrue :
  constructiveX6ComparisonConstructed ≡ true
constructiveX6ComparisonConstructedIsTrue = refl

deltaLineExtractionConstructedIsTrue : deltaLineExtractionConstructed ≡ true
deltaLineExtractionConstructedIsTrue = refl

allDeltaOrbitLinesConstructedIsTrue : allDeltaOrbitLinesConstructed ≡ true
allDeltaOrbitLinesConstructedIsTrue = refl

deltaBasisSpanningConstructedIsTrue : deltaBasisSpanningConstructed ≡ true
deltaBasisSpanningConstructedIsTrue = refl

------------------------------------------------------------------------
-- Strong theorem currently available: witnessed nonzero invariant subspaces
-- equal the full function module.
------------------------------------------------------------------------

witnessedInvariantSubspaceIsWholeCarrier :
  ∀ {Member}
    (inv : FunctionModule.HeisenbergInvariantSubspace Member) →
    (witness : DeltaExtraction.NonzeroInvariantVector inv) →
    (f : FunctionModule.SchrodingerFunction) →
    Member f
witnessedInvariantSubspaceIsWholeCarrier inv witness f =
  Basis.allDeltaLinesSpanEverySchrodingerFunction inv
    (Orbit.allBooleanDeltaLinesBelong inv witness)
    f

record FiniteStoneVonNeumannReceipt : Set where
  constructor finiteStoneVonNeumannReceipt
  field
    finiteHeisenbergGroupConstructed : Bool
    centreConstructedAndHasOrderThree : Bool
    commutatorPairingConstructedReceipt : Bool
    quotientPairingNondegenerate : Bool
    nontrivialCentralCharacterConstructed : Bool
    schrodingerRepresentationConstructed : Bool
    schrodingerRepresentationIrreducible : Bool
    uniquenessForFixedNontrivialCentralCharacter : Bool
open FiniteStoneVonNeumannReceipt public

record Certified729IdentificationReceipt : Set where
  constructor certified729IdentificationReceipt
  field
    stoneVonNeumann : FiniteStoneVonNeumannReceipt
    certifiedRestrictionHasNontrivialCentralCharacter : Bool
    certifiedRestrictionDegreeIs729 : Bool
    certifiedRepresentationIsomorphicToX6Model : Bool
open Certified729IdentificationReceipt public

record StoneVonNeumannFrontierBoundary : Set where
  constructor stoneVonNeumannFrontierBoundary
  field
    finiteHeisenbergGroupLawsFullyProvedHere : Bool
    globalNondegenerateCommutatorPairingProvedHere : Bool
    schrodingerFunctionModuleConstructedHere : Bool
    modulationDerivedPointProjectorConstructedHere : Bool
    projectorSelected729AndOffPointSemanticsOwnedHere : Bool
    nonzeroCyclotomicInverseOwnedHere : Bool
    deltaLineExtractionFromNonzeroInvariantSubspaceProvedHere : Bool
    translationOrbitReachesEveryDeltaLineProvedHere : Bool
    deltaBasisSpansFullFunctionCarrierProvedHere : Bool
    translatedDeltaOrbitSpansFullFunctionCarrierProvedHere : Bool
    witnessedInvariantSubspaceIsWholeCarrierProvedHere : Bool
    arbitraryNonzeroVectorYieldsSelectedNonzeroCoordinateHere : Bool
    irreducibilityOfX6SchrodingerModelProvedHere : Bool
    uniquenessForCentralCharacterProvedHere : Bool
    certifiedMonster729ConstituentIdentifiedWithX6Here : Bool
open StoneVonNeumannFrontierBoundary public

canonicalStoneVonNeumannFrontierBoundary : StoneVonNeumannFrontierBoundary
canonicalStoneVonNeumannFrontierBoundary =
  stoneVonNeumannFrontierBoundary
    true true true true true true
    true true true true true
    false false false false

data StoneVonNeumannProofLeaf : Set where
  constructCentralExtensionCarrier : StoneVonNeumannProofLeaf
  proveFiniteHeisenbergGroupLaws : StoneVonNeumannProofLeaf
  proveGlobalCommutatorNondegeneracy : StoneVonNeumannProofLeaf
  constructSchrodingerFunctionModule : StoneVonNeumannProofLeaf
  deriveModulationPointProjectors : StoneVonNeumannProofLeaf
  proveProjector729AndOffPointSemantics : StoneVonNeumannProofLeaf
  constructNonzeroCyclotomicInverse : StoneVonNeumannProofLeaf
  extractDeltaLineFromNonzeroInvariantSubspace : StoneVonNeumannProofLeaf
  proveTranslationOrbitReachesEveryDeltaLine : StoneVonNeumannProofLeaf
  proveDeltaBasisSpansCarrier : StoneVonNeumannProofLeaf
  proveTranslatedDeltaOrbitSpansCarrier : StoneVonNeumannProofLeaf
  proveWitnessedIrreducibility : StoneVonNeumannProofLeaf
  extractNonzeroCoordinateFromNonzeroVector : StoneVonNeumannProofLeaf
  proveSchrodingerIrreducible : StoneVonNeumannProofLeaf
  proveFixedCentralCharacterUniqueness : StoneVonNeumannProofLeaf
  identifyCertifiedMonster729Constituent : StoneVonNeumannProofLeaf

data LeafState : Set where closed open blocked : LeafState

leafState : StoneVonNeumannProofLeaf → LeafState
leafState constructCentralExtensionCarrier = closed
leafState proveFiniteHeisenbergGroupLaws = closed
leafState proveGlobalCommutatorNondegeneracy = closed
leafState constructSchrodingerFunctionModule = closed
leafState deriveModulationPointProjectors = closed
leafState proveProjector729AndOffPointSemantics = closed
leafState constructNonzeroCyclotomicInverse = closed
leafState extractDeltaLineFromNonzeroInvariantSubspace = closed
leafState proveTranslationOrbitReachesEveryDeltaLine = closed
leafState proveDeltaBasisSpansCarrier = closed
leafState proveTranslatedDeltaOrbitSpansCarrier = closed
leafState proveWitnessedIrreducibility = closed
leafState extractNonzeroCoordinateFromNonzeroVector = open
leafState proveSchrodingerIrreducible = blocked
leafState proveFixedCentralCharacterUniqueness = blocked
leafState identifyCertifiedMonster729Constituent = blocked

data Requires : StoneVonNeumannProofLeaf → StoneVonNeumannProofLeaf → Set where
  orbitNeedsExtraction :
    Requires proveTranslationOrbitReachesEveryDeltaLine
      extractDeltaLineFromNonzeroInvariantSubspace
  basisNeedsModule :
    Requires proveDeltaBasisSpansCarrier constructSchrodingerFunctionModule
  fullSpanningNeedsOrbit :
    Requires proveTranslatedDeltaOrbitSpansCarrier
      proveTranslationOrbitReachesEveryDeltaLine
  fullSpanningNeedsBasis :
    Requires proveTranslatedDeltaOrbitSpansCarrier proveDeltaBasisSpansCarrier
  witnessedIrreducibleNeedsSpanning :
    Requires proveWitnessedIrreducibility proveTranslatedDeltaOrbitSpansCarrier
  fullIrreducibleNeedsWitnessExtraction :
    Requires proveSchrodingerIrreducible extractNonzeroCoordinateFromNonzeroVector
  fullIrreducibleNeedsWitnessed :
    Requires proveSchrodingerIrreducible proveWitnessedIrreducibility
  uniquenessNeedsIrreducible :
    Requires proveFixedCentralCharacterUniqueness proveSchrodingerIrreducible
  identifyNeedsUniqueness :
    Requires identifyCertifiedMonster729Constituent proveFixedCentralCharacterUniqueness

highestImpactStructuralLeaf : StoneVonNeumannProofLeaf
highestImpactStructuralLeaf = extractNonzeroCoordinateFromNonzeroVector

highestImpactStructuralLeafIsOpen :
  leafState highestImpactStructuralLeaf ≡ open
highestImpactStructuralLeafIsOpen = refl
