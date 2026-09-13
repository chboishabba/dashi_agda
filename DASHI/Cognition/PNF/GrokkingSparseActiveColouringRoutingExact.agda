module DASHI.Cognition.PNF.GrokkingSparseActiveColouringRoutingExact where

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.GrokkingInvariantSubspaceSelectionExact as GrokSelect
import DASHI.Cognition.PNF.GrokkingMeasureStrataExact as GrokMeasure
import DASHI.Combinatorics.GraphColouringRecolourPantsSnowballExact as Colouring

------------------------------------------------------------------------
-- SPARSE ACTIVE SUPPORT / GROKKING / COLOURING ROUTING
--
-- This is a bounded structural bridge.  It does NOT identify MoE routing,
-- neuron sparsity, grokking dynamics, and graph colouring as one theorem.
-- Instead it records a shared finite pattern:
--
--   large available carrier
--     -> conditionally selected active support
--     -> compatibility / structural-defect constraint
--     -> task-relevant result.
--
-- The existing Grokking owners retain authority over training fit,
-- generalisation visibility, latent mechanism progress, and invariant-rule
-- selection.  The graph-colouring owner retains authority over the sourced
-- 2026 near-linear colouring claim and the reduction/lift/gluing snowball.
------------------------------------------------------------------------

record SparseSupportWitness : Set where
  constructor sparseSupportWitness
  field
    availableCapacity : Nat
    activeSupport : Nat

open SparseSupportWitness public

structuredSparseWitness : SparseSupportWitness
structuredSparseWitness = sparseSupportWitness 2 1

structuredSparseUsesStrictSubset :
  activeSupport structuredSparseWitness < availableCapacity structuredSparseWitness
structuredSparseUsesStrictSubset = s≤s (s≤s z≤n)

------------------------------------------------------------------------
-- Conditional inactivity is input-relative, not a global redundancy proof.
------------------------------------------------------------------------

record ConditionalUnitUse : Set where
  constructor conditionalUnitUse
  field
    inactiveForCurrentInput : Bool
    usefulOnAnotherInput : Bool

open ConditionalUnitUse public

conditionallyUsefulUnit : ConditionalUnitUse
conditionallyUsefulUnit = conditionalUnitUse true true

conditionalUseWitness :
  inactiveForCurrentInput conditionallyUsefulUnit ≡ true ×
  usefulOnAnotherInput conditionallyUsefulUnit ≡ true
conditionalUseWitness = refl , refl

inactiveNowDoesNotProveGlobalRedundancy : Bool
inactiveNowDoesNotProveGlobalRedundancy = true

------------------------------------------------------------------------
-- Reuse the exact existing grokking separation:
-- equal training fit does not determine invariant task geometry.
------------------------------------------------------------------------

data Route : Set where
  memorizerRoute : Route
  characterRoute : Route

routeCandidate : Route → GrokSelect.RepresentationCandidate
routeCandidate memorizerRoute = GrokSelect.memorizer
routeCandidate characterRoute = GrokSelect.characterRule

trainingFitSame : Route → Route → Bool
trainingFitSame memorizerRoute characterRoute = true
trainingFitSame characterRoute memorizerRoute = true
trainingFitSame memorizerRoute memorizerRoute = true
trainingFitSame characterRoute characterRoute = true

structuralDefect : Route → Nat
structuralDefect route = GrokSelect.invarianceDefect (routeCandidate route)

fitEqualButStructuralRouteImproves :
  trainingFitSame memorizerRoute characterRoute ≡ true ×
  structuralDefect characterRoute < structuralDefect memorizerRoute
fitEqualButStructuralRouteImproves =
  refl , GrokSelect.characterStrictlyImprovesInvariantGeometry

trainingTaskMechanismMassRemainDistinct : Bool
trainingTaskMechanismMassRemainDistinct = true

------------------------------------------------------------------------
-- Colouring cross-pollination.
--
-- `fourColourLinearReductionClaim` is source-attributed in the existing owner;
-- DASHI does not import the paper proof.  We use it only as the finite witness
-- that a large candidate family may expose many mutually compatible local
-- reductions while global correctness still requires the reduction/lift/glue
-- chain.
------------------------------------------------------------------------

colouringSourceClaim : Colouring.AttributedClaim
colouringSourceClaim = Colouring.fourColourLinearReductionClaim

colouringConflictFreeBatchWitness : Bool
colouringConflictFreeBatchWitness = true

grokkingLiterallyMinimisesChromaticNumber : Bool
grokkingLiterallyMinimisesChromaticNumber = false

colouringAnalogyBoundary :
  colouringConflictFreeBatchWitness ≡ true ×
  grokkingLiterallyMinimisesChromaticNumber ≡ false
colouringAnalogyBoundary = refl , refl

record CandidateActionRoutingWitness : Set where
  constructor candidateActionRoutingWitness
  field
    largeCandidateFamily : Bool
    sparseCompatibleAction : Bool
    globalCorrectnessStillNeedsLiftOrConsumer : Bool

open CandidateActionRoutingWitness public

colouringRoutingWitness : CandidateActionRoutingWitness
colouringRoutingWitness = candidateActionRoutingWitness true true true

colouringCandidateActionWitness :
  largeCandidateFamily colouringRoutingWitness ≡ true ×
  sparseCompatibleAction colouringRoutingWitness ≡ true
colouringCandidateActionWitness = refl , refl

------------------------------------------------------------------------
-- Promotion / WrongType boundary.
------------------------------------------------------------------------

record SparseActiveGrokkingBoundary : Set where
  constructor sparseActiveGrokkingBoundary
  field
    availableCapacityIsActiveCapacity : Bool
    inactiveForOneInputImpliesGloballyRedundant : Bool
    interpolationImpliesGeneralisation : Bool
    grokkingIsOrdinaryLossReduction : Bool
    sparseActivationImpliesPrunableEverywhere : Bool
    graphColouringCompatibilityIsMoERoutingIdentity : Bool
    graphChromaticNumberIsGrokkingObjective : Bool
    largeCandidateFamilyCanPermitSparseCompatibleAction : Bool
    overcompleteCarrierMaySupportConditionalReuse : Bool

open SparseActiveGrokkingBoundary public

canonicalSparseActiveGrokkingBoundary : SparseActiveGrokkingBoundary
canonicalSparseActiveGrokkingBoundary =
  sparseActiveGrokkingBoundary
    false
    false
    false
    false
    false
    false
    false
    true
    true

------------------------------------------------------------------------
-- The strongest exact statement paid here is deliberately modest:
--
-- * the existing finite grokking regression has two equally training-fitting
--   candidates but strictly different task-action defect;
-- * a finite support witness can use a strict subset of available capacity;
-- * current-input inactivity can coexist with usefulness elsewhere;
-- * the sourced colouring architecture supplies a compatible-batch analogy;
-- * none of those facts identifies the underlying optimization objectives.
------------------------------------------------------------------------
