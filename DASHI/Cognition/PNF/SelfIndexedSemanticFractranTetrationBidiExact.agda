module DASHI.Cognition.PNF.SelfIndexedSemanticFractranTetrationBidiExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin using (Fin)

import DASHI.Biology.SelfIndexingHyperfabricTetrationExact as Tower
import DASHI.Biology.TernaryHypercubeHyperfabricExact as Hyper
import DASHI.Cognition.PNF.BracketedTSFVFractranWorldFibreExact as World
import DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact as Context
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed

------------------------------------------------------------------------
-- Semantic self-indexing tower.
--
-- Ordinary product extension remains distinct from tetration.  Tetration is
-- used only when the complete previous-level carrier becomes the index set for
-- the next nine-valued observation field, exactly as in the existing owner.
------------------------------------------------------------------------

SemanticIndex : Nat → Set
SemanticIndex = Tower.SelfIndexedCarrier

semanticIndexCount : Nat → Nat
semanticIndexCount = Tower.selfIndexedSiteCount

semanticIndexCountIsNineTetration :
  (n : Nat) →
  semanticIndexCount n ≡ Hyper.nineTetration n
semanticIndexCountIsNineTetration = Tower.selfIndexedCountEqualsNineTetration

record SemanticSiteState : Set where
  constructor semanticSiteState
  field
    world : World.WorldHistory
    occurrence : Context.ContextualOccurrenceState
    residual : World.ResidualWorldFibre
    phasePrime : Signed.SSPPrime

open SemanticSiteState public

------------------------------------------------------------------------
-- A level carries both its coarse nine-valued field and a fine semantic fibre
-- over every self-indexed address.  The nine-valued carrier is an observation
-- address; it is not identified with the complete fine semantic state.
------------------------------------------------------------------------

record SemanticTetrationLevel (n : Nat) : Set₁ where
  constructor semanticTetrationLevel
  field
    coarseField : SemanticIndex n → Fin 9
    FineState : SemanticIndex n → Set
    fineState : (index : SemanticIndex n) → FineState index
    residualAt : SemanticIndex n → Set
    resolutionAt : SemanticIndex n → Tower.FabricResolution

open SemanticTetrationLevel public

record SemanticTowerStep (n : Nat) : Set₁ where
  constructor semanticTowerStep
  field
    before : SemanticTetrationLevel n
    after : SemanticTetrationLevel (suc n)

    -- The next carrier is the whole previous index carrier mapped into Fin 9;
    -- this witnesses the existing self-indexing recurrence rather than ordinary
    -- product/tensor replication.
    nextIndexIsField : SemanticIndex (suc n) ≡ (SemanticIndex n → Fin 9)

open SemanticTowerStep public

canonicalNextIndexIsField :
  (n : Nat) →
  SemanticIndex (suc n) ≡ (SemanticIndex n → Fin 9)
canonicalNextIndexIsField n = refl

------------------------------------------------------------------------
-- BIDI projection/reconstruction socket.  Projection may collapse many fine
-- worlds into one nine-valued site; reconstruction therefore returns a fibre,
-- not an invented unique world.
------------------------------------------------------------------------

record SemanticTetrationProjection (n : Nat) : Set₁ where
  constructor semanticTetrationProjection
  field
    Fine : Set
    project : Fine → SemanticIndex n → Fin 9
    Residual : Fine → Set
    reconstructFibre : (SemanticIndex n → Fin 9) → Set

open SemanticTetrationProjection public

------------------------------------------------------------------------
-- The phase/mode interpretation remains typed.  A local nine-state carrier may
-- be viewed through one fixed/trivial sector plus inverse-oriented pairs, but
-- no actual Monster representation is asserted by this carrier construction.
------------------------------------------------------------------------

data NinePhaseKind : Set where
  fixedTrivial : NinePhaseKind
  inversePairMember : NinePhaseKind

record NineModePhaseAddress : Set where
  constructor nineModePhaseAddress
  field
    coarseAddress : Fin 9
    phaseKind : NinePhaseKind

open NineModePhaseAddress public

------------------------------------------------------------------------
-- Boundaries inherited from the surrounding architecture.
------------------------------------------------------------------------

record SemanticTetrationBoundary : Set where
  constructor semanticTetrationBoundary
  field
    ordinaryProductGrowthIsTetration : Bool
    coarseNineStateIsCompleteFineState : Bool
    nextLevelIndexesWholePreviousCarrier : Bool
    fineFibresMayRemainHighDimensional : Bool
    sameCoarseAddressForcesSameWorld : Bool
    nineCarrierAutomaticallyMonsterRepresentation : Bool

canonicalSemanticTetrationBoundary : SemanticTetrationBoundary
canonicalSemanticTetrationBoundary =
  semanticTetrationBoundary false false true true false false
