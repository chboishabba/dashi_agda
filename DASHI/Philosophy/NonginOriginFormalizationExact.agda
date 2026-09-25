module DASHI.Philosophy.NonginOriginFormalizationExact where

------------------------------------------------------------------------
-- NONGIN ORIGIN FORMALISATION
--
-- Source basis:
--   user-supplied raw-origin transcript preserved as
--   Pasted text(20260826-134336).txt / "nongin.txt".
--
-- This module formalises only the structural content recoverable from that
-- stream:
--
--   recursive subdivision
--     -> hidden state-space behind a coarse binary presentation
--     -> one-more-frame / "1.0 -> 1.1" reflexive lift
--     -> historical "odds of odds" routed to existing probability/branching owners
--     -> recursive observer nesting
--     -> explicit information loss under dimensional projection.
--
-- It does NOT assert:
--   * a universal empirical 10-percent advantage;
--   * that 3/6/9 has a privileged physical law status;
--   * that later p-adic, tensor, dialectical, or physical constructions were
--     already mathematically proved by the historical transcript;
--   * that a richer representation guarantees better decisions or outcomes.
--
-- The historical genealogy remains owned by
-- DASHI.Core.DialecticOriginSourceAtlasExact.
-- The later 1.0 -> 1.1 frame-bearing construction remains owned by
-- DASHI.Philosophy.ReflexivePowerUp.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

open import DASHI.Core.Prelude using (⊥)
import DASHI.Core.DialecticOriginSourceAtlasExact as Origin
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.FiniteBranchingCriticalityExact as Branch
import DASHI.Core.FiniteTypedBranchingKernelExact as TypedBranch
import DASHI.Philosophy.ReflexivePowerUp as Reflexive
import DASHI.Reasoning.TrialecticBoundaryFaceNonfactorabilityExact as Trialectic
import DASHI.Reasoning.TrialecticEdgeSynthesisCompatibilityExact as TrialecticSynthesis
import DASHI.Foundations.TrialecticDepthHyperformExact as TrialecticDepth
import DASHI.Statistics.ForecastVerificationKernelExact as Forecast

------------------------------------------------------------------------
-- 1. Recursive subdivision.
------------------------------------------------------------------------

data Bit : Set where
  bit0 bit1 : Bit

BitPath : Set
BitPath = List Bit

refine0 : BitPath → BitPath
refine0 path = bit0 ∷ path

refine1 : BitPath → BitPath
refine1 path = bit1 ∷ path

data OneStepRefinement (parent : BitPath) : BitPath → Set where
  left-child  : OneStepRefinement parent (refine0 parent)
  right-child : OneStepRefinement parent (refine1 parent)

------------------------------------------------------------------------
-- 2. A coarse binary presentation can hide a larger state-space.
--
-- A lossy projection carries an explicit collision witness: two distinct fine
-- states are presented as the same coarse state.
------------------------------------------------------------------------

record LossyProjection (Fine Coarse : Set) : Set where
  constructor lossy-projection
  field
    project : Fine → Coarse
    hiddenLeft hiddenRight : Fine
    sameCoarse : project hiddenLeft ≡ project hiddenRight
    hiddenDistinct : hiddenLeft ≡ hiddenRight → ⊥

open LossyProjection public

------------------------------------------------------------------------
-- Minimal debate example: the public frame exposes only one participant's
-- binary coordinate while the latent state carries both coordinates.
------------------------------------------------------------------------

record DebateState : Set where
  constructor debate-state
  field
    self  : Bit
    other : Bit

open DebateState public

publicBinaryFrame : DebateState → Bit
publicBinaryFrame = self

debateHiddenStateWitness : LossyProjection DebateState Bit
debateHiddenStateWitness =
  lossy-projection
    publicBinaryFrame
    (debate-state bit0 bit0)
    (debate-state bit0 bit1)
    refl
    distinct
  where
  distinct :
    debate-state bit0 bit0 ≡ debate-state bit0 bit1 → ⊥
  distinct ()

------------------------------------------------------------------------
-- 2b. Mature trialectic descendant.
--
-- The historical binary/debate observation should not be re-derived as if the
-- repository lacked a relational owner.  The mature trialectic construction
-- is strictly stronger:
--
--   * three dyadic edge dispositions form only the boundary;
--   * an irreducible triadic face is retained beyond those edges;
--   * two whole trialectic states can have the same boundary and different
--     faces;
--   * at depth, distinct fine face/gluing states can truncate to one coarse
--     state.
--
-- This is a retrospective structural correspondence, not a claim that the raw
-- Nongin transcript already contained the later trialectic theorem.
------------------------------------------------------------------------

matureTrialecticNonfactorability :
  Descent.FactorsThrough
    Trialectic.boundaryObserver
    Trialectic.faceConsumer
  →
  ⊥
matureTrialecticNonfactorability =
  Trialectic.triadicFaceCannotFactorThroughThreeEdges

matureTrialecticCoarseCollision :
  TrialecticDepth.truncate
    TrialecticDepth.canonicalTrialecticDepthSystem
    zero
    TrialecticDepth.fineLayerLeft
  ≡
  TrialecticDepth.truncate
    TrialecticDepth.canonicalTrialecticDepthSystem
    zero
    TrialecticDepth.fineLayerRight
matureTrialecticCoarseCollision =
  TrialecticDepth.fineLayersCollideAtCoarseDepth


matureTrialecticEdgeSynthesisBoundary :
  TrialecticSynthesis.TrialecticEdgeSynthesisCompatibilityBoundary
matureTrialecticEdgeSynthesisBoundary =
  TrialecticSynthesis.canonicalTrialecticEdgeSynthesisCompatibilityBoundary

------------------------------------------------------------------------
-- 3. "1.0 -> 1.1" is a representational lift, not multiplication by 1.1.
--
-- A refinement embedding says that the richer carrier can represent every
-- lower-level state and can forget back to it exactly.
------------------------------------------------------------------------

record RepresentationLift (Lower Upper : Set) : Set where
  constructor representation-lift
  field
    embed  : Lower → Upper
    forget : Upper → Lower
    roundTrip : (x : Lower) → forget (embed x) ≡ x

open RepresentationLift public

record FrameBearing (X Frame : Set) : Set where
  constructor frame-bearing
  field
    object : X
    frame  : Frame

open FrameBearing public

frameBearingLift : {X Frame : Set} → Frame → RepresentationLift X (FrameBearing X Frame)
frameBearingLift defaultFrame =
  representation-lift
    (λ x → frame-bearing x defaultFrame)
    object
    (λ x → refl)

------------------------------------------------------------------------
-- The historical "+10%" label is retained as genealogy metadata only.
------------------------------------------------------------------------

record PowerUpBoundary : Set where
  constructor power-up-boundary
  field
    historicalLabel : String
    formalMeaning : String
    literalTenPercentLaw : Bool
    guaranteedOutcomeAdvantage : Bool

canonicalPowerUpBoundary : PowerUpBoundary
canonicalPowerUpBoundary =
  power-up-boundary
    "+10% / 1.1 versus 1.0"
    "one additional represented frame/meta-level with a forgetful map back to the lower representation"
    false
    false

------------------------------------------------------------------------
-- 4. Existing "odds of odds" owners.
--
-- Do not create a parallel ProbabilityOrder here.  The historical phrase is
-- already recorded by DialecticOriginSourceAtlasExact, while exact downstream
-- probability/odds and branching arithmetic have their own canonical owners:
--
--   ForecastVerificationKernelExact
--     Probability, OddsPair, OddsUpdateReceipt, OddsComparisonReceipt
--
--   FiniteBranchingCriticalityExact
--     scaled branch availability, independent-axis product arithmetic,
--     exact 11^3/10^3 gain regression, criticality boundary
--
--   FiniteTypedBranchingKernelExact
--     heterogeneous / varying-depth branching kernels.
--
-- Nongin therefore contributes provenance into those owners; it does not
-- redefine their mathematical carriers.
------------------------------------------------------------------------

historicalOddsEntry : Origin.OriginSourceEntry
historicalOddsEntry = Origin.oddsEntry

existingBranchingOddsBoundary : Branch.FiniteBranchingCriticalityBoundary
existingBranchingOddsBoundary =
  Branch.canonicalFiniteBranchingCriticalityBoundary

existingTypedBranchingBoundary : TypedBranch.FiniteTypedBranchingKernelBoundary
existingTypedBranchingBoundary =
  TypedBranch.canonicalFiniteTypedBranchingKernelBoundary

existingForecastOddsBoundary : Forecast.ForecastVerificationKernelBoundary
existingForecastOddsBoundary =
  Forecast.canonicalForecastVerificationKernelBoundary

------------------------------------------------------------------------
-- 5. Recursive observer nesting.
------------------------------------------------------------------------

data ObserverTerm (Observer X : Set) : Set where
  observed : X → ObserverTerm Observer X
  observes : Observer → ObserverTerm Observer X → ObserverTerm Observer X

oneObserver :
  {Observer X : Set} →
  Observer →
  X →
  ObserverTerm Observer X
oneObserver o x = observes o (observed x)

twoObservers :
  {Observer X : Set} →
  Observer →
  Observer →
  X →
  ObserverTerm Observer X
twoObservers outer inner x = observes outer (observes inner (observed x))

------------------------------------------------------------------------
-- 6. "Dimensional squishing" is explicit quotient/projection loss.
--
-- A higher-dimensional representation may distinguish states that a lower
-- chart identifies.  This is a structural theorem about the supplied
-- projection witness only; it is not a claim that "more dimensions" are
-- always epistemically superior.
------------------------------------------------------------------------

record HiddenDistinction (Fine Coarse : Set) : Set where
  constructor hidden-distinction
  field
    witness : LossyProjection Fine Coarse

open HiddenDistinction public

lossyProjectionHidesDistinction :
  {Fine Coarse : Set} →
  (p : LossyProjection Fine Coarse) →
  project p (hiddenLeft p) ≡ project p (hiddenRight p)
lossyProjectionHidesDistinction p = sameCoarse p

------------------------------------------------------------------------
-- 7. Bridge into the existing canonical reflexive owner.
--
-- This is deliberately thin: Nongin contributes the historical/generative
-- intuition, while ReflexivePowerUp owns the later exact frame-bearing record.
------------------------------------------------------------------------

nonginToReflexivePowerUp :
  {X Frame Residual Intervention : Set} →
  (x : X) →
  (frameOf : X → Frame) →
  Frame →
  Residual →
  Intervention →
  Set →
  Reflexive.ReflexiveKnowledge X Frame Residual Intervention
nonginToReflexivePowerUp =
  Reflexive.powerUp

------------------------------------------------------------------------
-- 8. Provenance and authority boundary.
------------------------------------------------------------------------

record NonginSourceBoundary : Set where
  constructor nongin-source-boundary
  field
    sourceClass : String
    sourceAnchor : String
    formalisationRelation : String
    externalScientificAuthority : Bool
    universalPhysicalLawClaimed : Bool
    laterTensorSemanticsRetroactivelyOriginal : Bool
    historicalBinaryToyIsIdenticalToMatureTrialectic : Bool
    nonginDefinesIndependentOddsHierarchy : Bool

canonicalNonginSourceBoundary : NonginSourceBoundary
canonicalNonginSourceBoundary =
  nongin-source-boundary
    "user-supplied raw origin / historical-genealogy source"
    "Pasted text(20260826-134336).txt; later reconstruction also names nongin.txt"
    "repository reconstruction of structural invariants; later exact modules retain independent theorem ownership"
    false
    false
    false
    false
    false

inheritedOriginBoundary : Origin.DialecticOriginSourceAtlasBoundary
inheritedOriginBoundary = Origin.canonicalDialecticOriginSourceAtlasBoundary
