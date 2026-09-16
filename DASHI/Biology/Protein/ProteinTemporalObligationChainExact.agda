module DASHI.Biology.Protein.ProteinTemporalObligationChainExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.Protein.TranslationContext as Translation
import DASHI.Biology.Protein.ProteinConformationAttractor as Conformation
import DASHI.Biology.Protein.ProteinFunctionProjection as Function
import DASHI.Biology.Protein.ProteinRecoveryBoundary as Recovery
import DASHI.Biology.Protein.ProteinSituatedHyperfabricExact as Situated
import DASHI.Biology.Cell.OpenMetabolicNetwork as Metabolism
import DASHI.Biology.Cell.CellStateAttractor as Cell

------------------------------------------------------------------------
-- PROTEIN TEMPORAL OBLIGATION CHAIN
--
-- Parent-level DASHI composition surface.  This is not a deterministic
-- central-dogma/metabolism pipeline and introduces no new empirical biology.
-- It keeps each promotion step as an explicit relation/payment so that a
-- downstream consumer cannot obtain expression, folding, flux, function or
-- history merely from the existence of an upstream state.
------------------------------------------------------------------------

record ProteinTemporalObligationChain : Set₁ where
  constructor protein-temporal-obligation-chain
  field
    EncodedState : Set
    TranslationState : Set
    RealisedProteinState : Set
    FoldingModificationState : Set
    LocalMetabolicEnvironmentState : Set
    ActionOutputState : Set
    HistoryResidualState : Set

    encodedToTranslation : EncodedState → TranslationState → Set
    translationToProtein : TranslationState → RealisedProteinState → Set
    proteinToFoldingModification : RealisedProteinState → FoldingModificationState → Set
    foldingToMetabolicContext : FoldingModificationState → LocalMetabolicEnvironmentState → Set
    metabolicContextToAction : LocalMetabolicEnvironmentState → ActionOutputState → Set
    actionToHistoryResidual : ActionOutputState → HistoryResidualState → Set
open ProteinTemporalObligationChain public

-- The propositions that pay each leg are application supplied.  The generic
-- owner does not manufacture them from adjacent states.
record ProteinTemporalObligations : Set₁ where
  constructor protein-temporal-obligations
  field
    ExpressionReceipt : Set
    TranslationReceipt : Set
    FoldingModificationReceipt : Set
    MetabolicFluxReceipt : Set
    FunctionalActionReceipt : Set
    HistoryRetentionReceipt : Set

    expressionReading : String
    translationReading : String
    foldingModificationReading : String
    metabolicFluxReading : String
    functionalActionReading : String
    historyReading : String
open ProteinTemporalObligations public

record ProteinTemporalChainWitness
  (C : ProteinTemporalObligationChain)
  (O : ProteinTemporalObligations) : Set₁ where
  constructor protein-temporal-chain-witness
  field
    encodedState : EncodedState C
    translationState : TranslationState C
    realisedProteinState : RealisedProteinState C
    foldingModificationState : FoldingModificationState C
    localMetabolicEnvironmentState : LocalMetabolicEnvironmentState C
    actionOutputState : ActionOutputState C
    historyResidualState : HistoryResidualState C

    encodedTranslationPaid : encodedToTranslation C encodedState translationState
    translationProteinPaid : translationToProtein C translationState realisedProteinState
    proteinFoldingPaid : proteinToFoldingModification C realisedProteinState foldingModificationState
    foldingMetabolicPaid : foldingToMetabolicContext C foldingModificationState localMetabolicEnvironmentState
    metabolicActionPaid : metabolicContextToAction C localMetabolicEnvironmentState actionOutputState
    actionHistoryPaid : actionToHistoryResidual C actionOutputState historyResidualState

    expressionReceipt : ExpressionReceipt O
    translationReceipt : TranslationReceipt O
    foldingModificationReceipt : FoldingModificationReceipt O
    metabolicFluxReceipt : MetabolicFluxReceipt O
    functionalActionReceipt : FunctionalActionReceipt O
    historyRetentionReceipt : HistoryRetentionReceipt O
open ProteinTemporalChainWitness public

------------------------------------------------------------------------
-- Existing repository surfaces are reused rather than redefined.
------------------------------------------------------------------------

translationContextSurface : Set₁
translationContextSurface = Translation.TranslationContext

conformationSystemSurface : Set₁
conformationSystemSurface = Conformation.ProteinConformationSystem

functionSystemSurface : Set₁
functionSystemSurface = Function.ProteinFunctionSystem

proteinRecoverySurface : Set₁
proteinRecoverySurface = Recovery.ProteinRecoveryBoundary

situatedProteinSurface : Set₁
situatedProteinSurface = Situated.ProteinSituatedHyperfabric

metabolismSurface : Set₁
metabolismSurface = Metabolism.OpenMetabolicNetwork

cellStateSurface : Set₁
cellStateSurface = Cell.CoupledCellState

------------------------------------------------------------------------
-- Explicit non-inference / WrongType boundaries.
------------------------------------------------------------------------

data GenomeDeterminesExpressedProtein : Set where
data SubstratePresenceDeterminesFlux : Set where
data ConformationDeterminesFunction : Set where
data VisibleStateDeterminesHistory : Set where
data TranslationDeterminesFold : Set where
data MetabolicFluxDeterminesAction : Set where
data TemporalChainCreatesEmpiricalMechanism : Set where
data ExternalIdentityPaysTemporalLeg : Set where

genomeDoesNotDetermineExpressedProtein : GenomeDeterminesExpressedProtein → ⊥
genomeDoesNotDetermineExpressedProtein ()

substrateDoesNotDetermineFlux : SubstratePresenceDeterminesFlux → ⊥
substrateDoesNotDetermineFlux ()

conformationDoesNotDetermineFunction : ConformationDeterminesFunction → ⊥
conformationDoesNotDetermineFunction ()

visibleStateDoesNotDetermineHistory : VisibleStateDeterminesHistory → ⊥
visibleStateDoesNotDetermineHistory ()

translationDoesNotDetermineFold : TranslationDeterminesFold → ⊥
translationDoesNotDetermineFold ()

metabolicFluxDoesNotDetermineAction : MetabolicFluxDeterminesAction → ⊥
metabolicFluxDoesNotDetermineAction ()

temporalChainDoesNotCreateEmpiricalMechanism : TemporalChainCreatesEmpiricalMechanism → ⊥
temporalChainDoesNotCreateEmpiricalMechanism ()

externalIdentityDoesNotPayTemporalLeg : ExternalIdentityPaysTemporalLeg → ⊥
externalIdentityDoesNotPayTemporalLeg ()

------------------------------------------------------------------------
-- Attribution discipline.
------------------------------------------------------------------------

attributionRule : String
attributionRule =
  "This temporal chain is DASHI synthesis over existing repository carriers. Empirical papers and datasets retain ownership only of their source-bounded propositions. DOI/PMID/PMCID/QID/PDB/UniProt are provenance/identity coordinates and cannot pay expression, folding, metabolic flux, function, mechanism or history obligations. Cross-pollination transfers structure only."

------------------------------------------------------------------------
-- Canonical boundary.
------------------------------------------------------------------------

record ProteinTemporalObligationBoundary : Set where
  constructor protein-temporal-obligation-boundary
  field
    translationSurfaceReused : Bool
    conformationSurfaceReused : Bool
    functionSurfaceReused : Bool
    proteinRecoverySurfaceReused : Bool
    situatedProteinSurfaceReused : Bool
    metabolismSurfaceReused : Bool
    cellStateSurfaceReused : Bool

    eachTemporalLegRequiresPayment : Bool
    historyResidualRetained : Bool

    genomeDeterminesExpressedProtein : Bool
    substratePresenceDeterminesFlux : Bool
    conformationDeterminesFunction : Bool
    visibleStateDeterminesHistory : Bool
    translationDeterminesFold : Bool
    metabolicFluxDeterminesAction : Bool
    compositionCreatesEmpiricalMechanism : Bool
    externalIdentityPaysTemporalLeg : Bool
open ProteinTemporalObligationBoundary public

canonicalProteinTemporalObligationBoundary : ProteinTemporalObligationBoundary
canonicalProteinTemporalObligationBoundary =
  protein-temporal-obligation-boundary
    true true true true true true true
    true true
    false false false false false false false false
