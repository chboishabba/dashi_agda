module DASHI.Cognition.PNF.DreamFlowRuntimeComplexityExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

------------------------------------------------------------------------
-- Symbolic work model for the theoretically optimized delta-native path.
--
-- N  parser/numeric input events
-- E  actually exposed local incidences / fibre interactions
-- R  emitted unresolved residual items
-- D  emitted semantic deltas
-- U  new global identities absent from the hot authority-backed cache
-- G  genuinely global/cross-fibre indexed operations
-- B  fused database boundary batches
-- H  semantic hierarchy depth
--
-- H is intentionally multiplied only by transported deltas, never by the size
-- of accumulated lower state.  The dream path rejects N*P and H*S accumulated-
-- state rescans as default execution shapes.
------------------------------------------------------------------------

record DreamWorkShape : Set where
  constructor dreamWorkShape
  field
    inputEvents : Nat
    exposedInteractions : Nat
    residualItems : Nat
    emittedDeltas : Nat
    coldIdentityMisses : Nat
    globalIndexedOperations : Nat
    databaseBatches : Nat
    hierarchyDepth : Nat

open DreamWorkShape public

localLinearWork : DreamWorkShape → Nat
localLinearWork work =
  inputEvents work
  + exposedInteractions work
  + residualItems work
  + emittedDeltas work

hierarchyTransportWork : DreamWorkShape → Nat
hierarchyTransportWork work =
  emittedDeltas work * hierarchyDepth work

boundaryWork : DreamWorkShape → Nat
boundaryWork work =
  coldIdentityMisses work
  + globalIndexedOperations work
  + databaseBatches work

idealDeclaredWork : DreamWorkShape → Nat
idealDeclaredWork work =
  localLinearWork work
  + hierarchyTransportWork work
  + boundaryWork work

------------------------------------------------------------------------
-- Constant-depth specialization.
--
-- For a fixed PNF hierarchy schema, H is an architecture constant.  The
-- hierarchy term is then linear in D rather than a rescan of accumulated state.
------------------------------------------------------------------------

record FixedHierarchyDepth (work : DreamWorkShape) : Set where
  field
    fixedDepth : Nat
    depthIsFixed : hierarchyDepth work ≡ fixedDepth

open FixedHierarchyDepth public

------------------------------------------------------------------------
-- Forbidden default amplification shapes.
------------------------------------------------------------------------

data DemandProfileCartesianRequired : Set where

data HierarchyAccumulatedStateRescanRequired : Set where

data PerEventDatabaseRoundTripRequired : Set where

data FullCorpusLookupPerEventRequired : Set where

cartesianCandidateMaterializationIsNotRequired :
  DemandProfileCartesianRequired → ∀ {A : Set} → A
cartesianCandidateMaterializationIsNotRequired ()

hierarchyRescanIsNotRequired :
  HierarchyAccumulatedStateRescanRequired → ∀ {A : Set} → A
hierarchyRescanIsNotRequired ()

perEventDatabaseRoundTripIsNotRequired :
  PerEventDatabaseRoundTripRequired → ∀ {A : Set} → A
perEventDatabaseRoundTripIsNotRequired ()

fullCorpusLookupPerEventIsNotRequired :
  FullCorpusLookupPerEventRequired → ∀ {A : Set} → A
fullCorpusLookupPerEventIsNotRequired ()

------------------------------------------------------------------------
-- Work-factorization receipt.
--
-- Runtime instrumentation should classify measured operations into these terms.
-- Wall clock is evaluated only after this structural work shape is known.
------------------------------------------------------------------------

record DreamWorkReceipt : Set where
  constructor dreamWorkReceipt
  field
    shape : DreamWorkShape
    parserProjectionWork : Nat
    localSolverWork : Nat
    deltaTransportMeasuredWork : Nat
    residualMeasuredWork : Nat
    globalLookupMeasuredWork : Nat
    publicationMeasuredWork : Nat

open DreamWorkReceipt public

measuredDeclaredWork : DreamWorkReceipt → Nat
measuredDeclaredWork receipt =
  parserProjectionWork receipt
  + localSolverWork receipt
  + deltaTransportMeasuredWork receipt
  + residualMeasuredWork receipt
  + globalLookupMeasuredWork receipt
  + publicationMeasuredWork receipt

------------------------------------------------------------------------
-- Near-parser performance target is a physical theorem/receipt, not derived from
-- asymptotics alone.  The concrete runtime supplies the order relation and the
-- requested ratio.  For example, with ordinary natural-number order, numerator
-- 6 and denominator 5 expresses post-parser <= 1.2 * parser.
------------------------------------------------------------------------

record NearParserWallTarget (_≤W_ : Nat → Nat → Set) : Set where
  constructor nearParserWallTarget
  field
    parserWall : Nat
    postParserWall : Nat
    allowedNumerator : Nat
    allowedDenominator : Nat
    targetWitness :
      postParserWall * allowedDenominator
        ≤W parserWall * allowedNumerator

open NearParserWallTarget public

------------------------------------------------------------------------
-- Structural complexity and measured wall performance remain independent.
------------------------------------------------------------------------

data LinearDeclaredWorkImpliesNearParserWall : Set where

linearWorkAloneCannotManufactureWallTarget :
  LinearDeclaredWorkImpliesNearParserWall → ∀ {A : Set} → A
linearWorkAloneCannotManufactureWallTarget ()
