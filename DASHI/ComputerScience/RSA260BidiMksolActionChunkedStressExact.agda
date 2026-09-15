module DASHI.ComputerScience.RSA260BidiMksolActionChunkedStressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiMksolActionSparseObserverExact as Sparse
import DASHI.ComputerScience.RSA260BidiConsumerHypergraphRoadmapExact as Roadmap

------------------------------------------------------------------------
-- CHUNKED STRESS OF THE CURRENT ACTION-CONSUMER HYPOTHESIS
--
-- The current twelve-world finite action portfolio has the unique size-two
-- hitting set {r2,r10}.  A wider 34-world action recomputation was attempted
-- but stopped after a partial prefix, so no portfolio pass/failure is paid.
--
-- This owner does not fabricate the missing runtime values.  It replaces one
-- monolithic wider run by a bounded receipt protocol.  Every chunk must be
-- complete before it may contribute edges to the enlarged hypergraph; only a
-- complete merged portfolio may promote or refute (degree,r2,r10).
------------------------------------------------------------------------

data ActionStressChunk : Set where
  worlds00to07 : ActionStressChunk
  worlds08to15 : ActionStressChunk
  worlds16to23 : ActionStressChunk
  worlds24to33 : ActionStressChunk

record ChunkExecutionReceipt : Set where
  constructor chunk-execution-receipt
  field
    chunk : ActionStressChunk
    expectedWorldCount : Nat
    completedWorldCount : Nat
    complete : Bool
    actionOutputsRetained : Bool
    rankR2Retained : Bool
    rankR10Retained : Bool
    allUniversallyAvailableRankCoordinatesRetained : Bool
    receiptReference : String
open ChunkExecutionReceipt public

chunkExpectedWorldCount : ActionStressChunk -> Nat
chunkExpectedWorldCount worlds00to07 = 8
chunkExpectedWorldCount worlds08to15 = 8
chunkExpectedWorldCount worlds16to23 = 8
chunkExpectedWorldCount worlds24to33 = 10

chunkPlanWorldCount : Nat
chunkPlanWorldCount =
  chunkExpectedWorldCount worlds00to07
  + chunkExpectedWorldCount worlds08to15
  + chunkExpectedWorldCount worlds16to23
  + chunkExpectedWorldCount worlds24to33

chunkPlanWorldCountIsThirtyFour : chunkPlanWorldCount ≡ 34
chunkPlanWorldCountIsThirtyFour = refl

------------------------------------------------------------------------
-- No partial-prefix promotion.
------------------------------------------------------------------------

data PartialPrefixCreatesPortfolioReceipt : Set where
data TwoRankSuccessOnTwelveCreatesThirtyFourWorldAdequacy : Set where
data RuntimeHypergraphCreatesGenericTheorem : Set where
data SyntheticActionCreatesCADOSameObjectContext : Set where

partialPrefixDoesNotCreatePortfolioReceipt :
  PartialPrefixCreatesPortfolioReceipt -> ⊥
partialPrefixDoesNotCreatePortfolioReceipt ()

twelveWorldSuccessDoesNotCreateThirtyFourWorldAdequacy :
  TwoRankSuccessOnTwelveCreatesThirtyFourWorldAdequacy -> ⊥
twelveWorldSuccessDoesNotCreateThirtyFourWorldAdequacy ()

runtimeHypergraphDoesNotCreateGenericTheorem :
  RuntimeHypergraphCreatesGenericTheorem -> ⊥
runtimeHypergraphDoesNotCreateGenericTheorem ()

syntheticActionDoesNotCreateCADOSameObjectContext :
  SyntheticActionCreatesCADOSameObjectContext -> ⊥
syntheticActionDoesNotCreateCADOSameObjectContext ()

------------------------------------------------------------------------
-- Bidi outcome: either the candidate survives every completed action edge, or
-- a collision gives the next residual-localisation witness.  The latter is a
-- feature: failure localises information that the action consumer actually
-- needs rather than sending us back to receipt-identity overfitting.
------------------------------------------------------------------------

data BroaderStressOutcome : Set where
  candidateSurvivesCompletePortfolio : BroaderStressOutcome
  candidateCollisionLocalizesResidual : BroaderStressOutcome
  portfolioStillIncomplete : BroaderStressOutcome

currentBroaderStressOutcome : BroaderStressOutcome
currentBroaderStressOutcome = portfolioStillIncomplete

record MksolActionChunkedStressBoundary : Set where
  constructor mksol-action-chunked-stress-boundary
  field
    chunkedExecutionPlanDefined : Bool
    targetWorldCountIsThirtyFour : Bool
    degreeR2R10HypothesisRetained : Bool
    partialPrefixIsNotPortfolioReceipt : Bool
    collisionWouldLocalizeNextCoordinate : Bool
    completeThirtyFourWorldActionReceiptPaid : Bool
    degreeR2R10BroaderAdequacyPaid : Bool
    exactCADOMksolSameObjectContextPaid : Bool
    nextResidual : String
open MksolActionChunkedStressBoundary public

canonicalMksolActionChunkedStressBoundary : MksolActionChunkedStressBoundary
canonicalMksolActionChunkedStressBoundary =
  mksol-action-chunked-stress-boundary
    true true true true true
    false false false
    "execute four bounded action-consumer chunks over the 34-world seed/adaptor portfolio; retain action output plus r2/r10 and the full available-rank vector for every world; merge only complete chunk receipts; rebuild consumer-separated hypergraph edges; if (degree,r2,r10) misses an edge, use that exact collision to localize the next coordinate. Do not promote a partial prefix, a twelve-world receipt, or synthetic action semantics to production CADO adequacy."

sparseBoundary : Sparse.MksolActionSparseObserverBoundary
sparseBoundary = Sparse.canonicalMksolActionSparseObserverBoundary

roadmapBoundary : Roadmap.ConsumerHypergraphRoadmapBoundary
roadmapBoundary = Roadmap.canonicalConsumerHypergraphRoadmapBoundary
