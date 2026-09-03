module DASHI.Culture.IntellectualReceptionSemanticStabiliserParetoAuthorityCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Culture.IntellectualReceptionActionVoxelGovernedSymmetryExact as Voxel
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Governance.AuthorityMandateCore as Authority
import DASHI.Governance.ContestedAmbientAuthorityHyperformalismExact as Contested
import DASHI.Moonshine.Base369Ternary27SignedSymmetryMonsterIntertwinerExact as Signed
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as Spectral

------------------------------------------------------------------------
-- SEMANTIC STABILISER / AUTHORITY CROSS-POLLINATION
--
-- The merged action-voxel owner already fixes the typed roles
--
--   x = comparison outcome
--   y = response policy
--   z = independent-authority status.
--
-- This file classifies a finite generator fragment.  It deliberately does not
-- claim that the repository has constructed the full signed-permutation group,
-- a full stabiliser subgroup, or a Monster representation.
------------------------------------------------------------------------

data GeometricGenerator : Set where
  identityGenerator
  comparisonFlipXGenerator
  swapXYGenerator
  rotateXYZGenerator
  : GeometricGenerator

applyGeometricGenerator :
  GeometricGenerator →
  Geometry.Ternary27Point →
  Geometry.Ternary27Point
applyGeometricGenerator identityGenerator point = point
applyGeometricGenerator comparisonFlipXGenerator point = Signed.flipX point
applyGeometricGenerator swapXYGenerator point = Spectral.swapXY point
applyGeometricGenerator rotateXYZGenerator point = Spectral.rotateXYZ point

------------------------------------------------------------------------
-- Semantic-role preservation is stricter than carrier geometry.
--
-- Identity and comparison reflection preserve the typed response/authority
-- roles.  Coordinate permutations are geometrically valid but are not granted
-- semantic-role preservation merely from that fact.
------------------------------------------------------------------------

data SemanticRolePreservingGenerator : GeometricGenerator → Set where
  semanticIdentity :
    SemanticRolePreservingGenerator identityGenerator
  semanticComparisonReflection :
    SemanticRolePreservingGenerator comparisonFlipXGenerator

applySemanticGenerator :
  ∀ {generator} →
  SemanticRolePreservingGenerator generator →
  Voxel.ActionVoxelState →
  Voxel.ActionVoxelState
applySemanticGenerator semanticIdentity state = state
applySemanticGenerator semanticComparisonReflection state =
  Voxel.reflectComparisonOnly state

semanticGeneratorAgreesWithGeometry :
  ∀ {generator} →
  (lawful : SemanticRolePreservingGenerator generator) →
  (state : Voxel.ActionVoxelState) →
  Voxel.actionVoxelPoint (applySemanticGenerator lawful state)
  ≡ applyGeometricGenerator generator (Voxel.actionVoxelPoint state)
semanticGeneratorAgreesWithGeometry semanticIdentity state = refl
semanticGeneratorAgreesWithGeometry semanticComparisonReflection state =
  Voxel.reflectComparisonAgreesWithVoxelFlipX state

swapXYIsGeometricallyAvailable :
  applyGeometricGenerator swapXYGenerator (Voxel.actionVoxelPoint Voxel.seekState)
  ≡ Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspNegOne
swapXYIsGeometricallyAvailable = Voxel.seekPointSwappedXY

swapXYNotSemanticRolePreserving :
  SemanticRolePreservingGenerator swapXYGenerator → ⊥
swapXYNotSemanticRolePreserving ()

rotateXYZNotSemanticRolePreserving :
  SemanticRolePreservingGenerator rotateXYZGenerator → ⊥
rotateXYZNotSemanticRolePreserving ()

------------------------------------------------------------------------
-- Independent authority is a further gate, not a consequence of semantic
-- preservation.  The current finite fixture authorises only the identity
-- generator.  This is a statement about this declared fixture, not a theorem
-- that comparison reflection can never be authorised in another context.
------------------------------------------------------------------------

data CanonicalFixtureAuthorityScope :
  Authority.AuthoritySource →
  GeometricGenerator →
  Set where
  fixtureIdentityScope :
    CanonicalFixtureAuthorityScope
      Authority.constitutionalDelegation
      identityGenerator

record CanonicalFixtureAuthorisedGenerator
    (generator : GeometricGenerator) : Set where
  constructor fixture-authorised-generator
  field
    source : Authority.AuthoritySource
    sourceAdmissible : Authority.AdmissibleAuthoritySource source
    inScope : CanonicalFixtureAuthorityScope source generator

open CanonicalFixtureAuthorisedGenerator public

identityFixtureAuthorised :
  CanonicalFixtureAuthorisedGenerator identityGenerator
identityFixtureAuthorised =
  fixture-authorised-generator
    Authority.constitutionalDelegation
    tt
    fixtureIdentityScope

fixtureAuthorisedImpliesSemantic :
  ∀ {generator} →
  CanonicalFixtureAuthorisedGenerator generator →
  SemanticRolePreservingGenerator generator
fixtureAuthorisedImpliesSemantic
  (fixture-authorised-generator source admissible fixtureIdentityScope) =
  semanticIdentity

comparisonReflectionNotFixtureAuthorised :
  CanonicalFixtureAuthorisedGenerator comparisonFlipXGenerator → ⊥
comparisonReflectionNotFixtureAuthorised
  (fixture-authorised-generator source admissible ())

swapXYNotFixtureAuthorised :
  CanonicalFixtureAuthorisedGenerator swapXYGenerator → ⊥
swapXYNotFixtureAuthorised
  (fixture-authorised-generator source admissible ())

-- #603 cross-pollination: recognition still cannot self-issue an authority
-- source.  A carrier symmetry therefore cannot obtain fixture authority merely
-- by being recognised by another carrier/interface.
externalRecognitionStillDoesNotCreateAuthority :
  Authority.AdmissibleAuthoritySource Authority.externalRecognitionAlone →
  Authority.Never
externalRecognitionStillDoesNotCreateAuthority =
  Contested.recognitionAloneDoesNotCreateAmbientAuthority

------------------------------------------------------------------------
-- #647 cross-pollination: ranking comes only after hard admissibility and
-- consumer/authority adequacy.  Here the model carrier is the finite generator
-- fragment itself.
------------------------------------------------------------------------

generatorReference : GeometricGenerator → String
generatorReference identityGenerator = "identity"
generatorReference comparisonFlipXGenerator = "comparison flip X"
generatorReference swapXYGenerator = "swap X/Y"
generatorReference rotateXYZGenerator = "rotate X/Y/Z"

generatorDescriptionLength : GeometricGenerator → Nat
generatorDescriptionLength identityGenerator = 0
generatorDescriptionLength comparisonFlipXGenerator = 1
generatorDescriptionLength swapXYGenerator = 1
generatorDescriptionLength rotateXYZGenerator = 1

generatorEligibilityProblem : MDL.ConsumerMDLProblem
generatorEligibilityProblem =
  MDL.consumerMDLProblem
    GeometricGenerator
    SemanticRolePreservingGenerator
    CanonicalFixtureAuthorisedGenerator
    generatorDescriptionLength
    (λ _ _ → ⊤)
    generatorReference
    "finite generator names only; no group presentation claimed"
    "canonical reception action-voxel authority fixture"

identityGeneratorEligible :
  MDL.Eligible generatorEligibilityProblem identityGenerator
identityGeneratorEligible =
  semanticIdentity , identityFixtureAuthorised

comparisonReflectionSemanticallyAdmissible :
  MDL.Admissible generatorEligibilityProblem comparisonFlipXGenerator
comparisonReflectionSemanticallyAdmissible =
  semanticComparisonReflection

comparisonReflectionNotEligibleInCurrentAuthorityFixture :
  MDL.Eligible generatorEligibilityProblem comparisonFlipXGenerator → ⊥
comparisonReflectionNotEligibleInCurrentAuthorityFixture eligible =
  comparisonReflectionNotFixtureAuthorised (proj₂ eligible)

swapXYNotEligible :
  MDL.Eligible generatorEligibilityProblem swapXYGenerator → ⊥
swapXYNotEligible eligible =
  swapXYNotSemanticRolePreserving (proj₁ eligible)

-- The generic Pareto layer is retained literally: only eligible models may be
-- selected by ParetoAdmissible.  No carrier symmetry can skip the semantic or
-- authority gates by having an attractive cost coordinate.
paretoEligibilityGateRetained :
  ∀ {selected} {costs : MDL.CostHyperfabric generatorEligibilityProblem} →
  MDL.ParetoAdmissible costs selected →
  MDL.Eligible generatorEligibilityProblem selected
paretoEligibilityGateRetained receipt =
  MDL.selectedEligible receipt

comparisonReflectionCannotBecomeParetoSelectedWithoutAuthority :
  ∀ {costs : MDL.CostHyperfabric generatorEligibilityProblem} →
  MDL.ParetoAdmissible costs comparisonFlipXGenerator → ⊥
comparisonReflectionCannotBecomeParetoSelectedWithoutAuthority receipt =
  comparisonReflectionNotEligibleInCurrentAuthorityFixture
    (paretoEligibilityGateRetained receipt)

swapXYCannotBecomeParetoSelectedByCheapGeometry :
  ∀ {costs : MDL.CostHyperfabric generatorEligibilityProblem} →
  MDL.ParetoAdmissible costs swapXYGenerator → ⊥
swapXYCannotBecomeParetoSelectedByCheapGeometry receipt =
  swapXYNotEligible (paretoEligibilityGateRetained receipt)

------------------------------------------------------------------------
-- Strict generator-fragment hierarchy.
------------------------------------------------------------------------

semanticFragmentStrictlySmallerThanGeometric :
  SemanticRolePreservingGenerator swapXYGenerator → ⊥
semanticFragmentStrictlySmallerThanGeometric =
  swapXYNotSemanticRolePreserving

authorisedFragmentStrictlySmallerThanSemantic :
  CanonicalFixtureAuthorisedGenerator comparisonFlipXGenerator → ⊥
authorisedFragmentStrictlySmallerThanSemantic =
  comparisonReflectionNotFixtureAuthorised

data GeneratorFragmentIsFullSymmetryGroup : Set where
data SemanticRolePreservationCreatesAuthority : Set where
data ParetoCostCreatesEligibility : Set where
data GeneratorFragmentIsMonsterRepresentation : Set where

generatorFragmentDoesNotClaimFullGroup :
  GeneratorFragmentIsFullSymmetryGroup → ⊥
generatorFragmentDoesNotClaimFullGroup ()

semanticRolePreservationDoesNotCreateAuthority :
  SemanticRolePreservationCreatesAuthority → ⊥
semanticRolePreservationDoesNotCreateAuthority ()

paretoCostDoesNotCreateEligibility :
  ParetoCostCreatesEligibility → ⊥
paretoCostDoesNotCreateEligibility ()

generatorFragmentDoesNotBecomeMonsterRepresentation :
  GeneratorFragmentIsMonsterRepresentation → ⊥
generatorFragmentDoesNotBecomeMonsterRepresentation ()

record IntellectualReceptionSemanticStabiliserParetoAuthorityBoundary : Set where
  constructor intellectual-reception-semantic-stabiliser-pareto-authority-boundary
  field
    geometricGeneratorFragmentExists : Bool
    comparisonReflectionPreservesTypedSemanticRoles : Bool
    coordinatePermutationAutomaticallyPreservesSemanticRoles : Bool
    semanticRolePreservationAutomaticallyCreatesAuthority : Bool
    currentFixtureAuthorisesComparisonReflection : Bool
    paretoRankingOccursOnlyAfterEligibility : Bool
    cheapGeometricMoveCanSkipSemanticGate : Bool
    recognitionAloneCreatesAuthority : Bool
    generatorFragmentIsFullSymmetryGroup : Bool
    generatorFragmentIsMonsterRepresentation : Bool
    sourceAttributionBoundarySurvives : Bool

canonicalIntellectualReceptionSemanticStabiliserParetoAuthorityBoundary :
  IntellectualReceptionSemanticStabiliserParetoAuthorityBoundary
canonicalIntellectualReceptionSemanticStabiliserParetoAuthorityBoundary =
  intellectual-reception-semantic-stabiliser-pareto-authority-boundary
    true true false false false true false false false false true
