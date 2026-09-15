module DASHI.ComputerScience.RSA260BidiMksolAction34WorldStressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiMksolActionChunkedStressExact as Chunked
import DASHI.ComputerScience.RSA260BidiMksolActionChunkMergeExact as Merge

------------------------------------------------------------------------
-- COMPLETE 34-WORLD SYNTHETIC MKSOL-STYLE ACTION STRESS
--
-- Runtime execution completed the previously unpaid 8+8+8+10 chunk protocol.
-- Every world retained degree, the full universally available coefficient-rank
-- vector, and a digest of the synthetic action
--
--   A(F;M,V) = xor_{l<d} M^l V F_l.
--
-- This action is a finite synthetic consumer only.  It is NOT claimed to be
-- exact CADO `mksol`, and it carries no production RSA-260 same-object
-- authority.
--
-- The earlier 12-world finite observer (degree,r2,r10) fails on this broadened
-- 34-world action family.  The finite action-separating hypergraph has 258
-- equal-degree/distinct-action pair constraints.  Exhaustive runtime search on
-- the universally available rank coordinates finds first separating size 5,
-- with 26 size-five transversals.  These are runtime portfolio facts, not a
-- generic minimum theorem.
------------------------------------------------------------------------

runtimeScriptPath : String
runtimeScriptPath = "/mnt/data/rsa260_bidi_mksol_action_34world_stress.py"

runtimeScriptSHA256 : String
runtimeScriptSHA256 =
  "6bb2492e3ba2444c58a85eb9ce422cdc17dd2b39b4257d99d2dad0975e69d298"

runtimeOutputPath : String
runtimeOutputPath = "/mnt/data/rsa260_bidi_mksol_action_34world_stress.json"

runtimeOutputSHA256 : String
runtimeOutputSHA256 =
  "e88a60056f28e6168ead0aa6f468c3ec6eb08b1e2dcb371d29ad8d58f05f1855"

completedChunk00to07 : Nat
completedChunk00to07 = 8

completedChunk08to15 : Nat
completedChunk08to15 = 8

completedChunk16to23 : Nat
completedChunk16to23 = 8

completedChunk24to33 : Nat
completedChunk24to33 = 10

completedWorldCount : Nat
completedWorldCount =
  completedChunk00to07 + completedChunk08to15
  + completedChunk16to23 + completedChunk24to33

completedWorldCountIsThirtyFour : completedWorldCount ≡ 34
completedWorldCountIsThirtyFour = refl

------------------------------------------------------------------------
-- Explicit action-consumer collision for the previous coarse observer.
------------------------------------------------------------------------

data CollisionWorld : Set where
  seed7 : CollisionWorld
  seed8 : CollisionWorld

collisionDegree : CollisionWorld -> Nat
collisionDegree seed7 = 16
collisionDegree seed8 = 16

collisionR2 : CollisionWorld -> Nat
collisionR2 seed7 = 7
collisionR2 seed8 = 7

collisionR10 : CollisionWorld -> Nat
collisionR10 seed7 = 7
collisionR10 seed8 = 7

-- We only need a finite separating action receipt for the formal defect.  The
-- full runtime SHA digests remain in the hash-bound JSON receipt above.
data ActionReceipt : Set where
  actionSeed7 : ActionReceipt
  actionSeed8 : ActionReceipt

collisionAction : CollisionWorld -> ActionReceipt
collisionAction seed7 = actionSeed7
collisionAction seed8 = actionSeed8

sameDegree : collisionDegree seed7 ≡ collisionDegree seed8
sameDegree = refl

sameR2 : collisionR2 seed7 ≡ collisionR2 seed8
sameR2 = refl

sameR10 : collisionR10 seed7 ≡ collisionR10 seed8
sameR10 = refl

actionReceiptsDiffer : Neg (collisionAction seed7 ≡ collisionAction seed8)
actionReceiptsDiffer ()

------------------------------------------------------------------------
-- WrongType / promotion firewalls.
------------------------------------------------------------------------

data RuntimeMinimumCreatesGenericTheorem : Set where
data SyntheticActionCreatesExactCADOMksolSemantics : Set where
data SyntheticActionCreatesProductionRSA260Adequacy : Set where
data ThirtyFourWorldFailureInvalidatesExactReplay : Set where

runtimeMinimumDoesNotCreateGenericTheorem :
  RuntimeMinimumCreatesGenericTheorem -> ⊥
runtimeMinimumDoesNotCreateGenericTheorem ()

syntheticActionDoesNotCreateCADOSemantics :
  SyntheticActionCreatesExactCADOMksolSemantics -> ⊥
syntheticActionDoesNotCreateCADOSemantics ()

syntheticActionDoesNotCreateProductionAdequacy :
  SyntheticActionCreatesProductionRSA260Adequacy -> ⊥
syntheticActionDoesNotCreateProductionAdequacy ()

stressFailureDoesNotInvalidateExactReplay :
  ThirtyFourWorldFailureInvalidatesExactReplay -> ⊥
stressFailureDoesNotInvalidateExactReplay ()

record MksolAction34WorldStressBoundary : Set where
  constructor mksol-action-34-world-stress-boundary
  field
    chunkPlanInherited : Bool
    completeThirtyFourWorldActionReceiptPaid : Bool
    completeWorldCount : Nat
    fullRankVectorsRetained : Bool
    actionOutputsRetained : Bool

    degreeR2R10BroaderAdequacyPaid : Bool
    explicitDegreeR2R10ActionCollisionPaid : Bool

    equalDegreeDistinctActionPairCount : Nat
    runtimeMinimumRankCoordinateCountFoundWithDegree : Nat
    runtimeSizeFiveTransversalCount : Nat

    runtimeMinimumCreatesGenericTheorem : Bool
    syntheticActionCreatesExactCADOMksolSemantics : Bool
    syntheticActionCreatesProductionRSA260Adequacy : Bool
    exactReplayRemainsSufficientUpperEndpoint : Bool

    nextResidual : String
open MksolAction34WorldStressBoundary public

canonicalMksolAction34WorldStressBoundary : MksolAction34WorldStressBoundary
canonicalMksolAction34WorldStressBoundary =
  mksol-action-34-world-stress-boundary
    true
    true
    34
    true
    true
    false
    true
    258
    5
    26
    false
    false
    false
    true
    "retire (degree,r2,r10) as a broader-family candidate; prefer the declared consumer-family intersection-kernel formulation. Use five-coordinate rank transversals only as finite diagnostics unless a downstream consumer explicitly benefits from them. Bind the generic Lean joint-kernel theorem only after its kernel receipt and the relevant RSA consumer-family binding are both paid."

chunkBoundary : Chunked.MksolActionChunkedStressBoundary
chunkBoundary = Chunked.canonicalMksolActionChunkedStressBoundary

mergeBoundary : Merge.MksolActionChunkMergeBoundary
mergeBoundary = Merge.canonicalMksolActionChunkMergeBoundary
