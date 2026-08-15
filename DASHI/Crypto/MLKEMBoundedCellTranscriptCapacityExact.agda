module DASHI.Crypto.MLKEMBoundedCellTranscriptCapacityExact where

------------------------------------------------------------------------
-- ML-KEM: BOUNDED CELL + TRANSCRIPT CAPACITY
--
-- If an exact maintained state consists of at most m cells, each drawn from an
-- alphabet of cardinality A, then its raw state carrier has at most A^m codes.
-- Likewise, a depth-d transcript whose each step has at most B outcomes has at
-- most B^d leaves.  Thus any exact protected-label recovery factoring through
-- state x transcript has capacity bounded by
--
--     A^m * B^d.
--
-- This module packages the numerical composition.  The actual finite-carrier
-- counting maps for a concrete verifier/query architecture remain explicit
-- premises; no information capacity is inferred merely from touch count.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_; _*_; _^_)
import Data.Nat.Properties as NatP

import DASHI.Crypto.MLKEMFiniteStateTranscriptCapacityExact as Capacity

stateCellCapacity : Nat → Nat → Nat
stateCellCapacity alphabetSize cellCount = alphabetSize ^ cellCount

transcriptLeafCapacity : Nat → Nat → Nat
transcriptLeafCapacity branchAlphabet depth = branchAlphabet ^ depth

combinedStateTranscriptCapacity : Nat → Nat → Nat → Nat → Nat
combinedStateTranscriptCapacity
  stateAlphabet stateCells transcriptAlphabet transcriptDepth =
  stateCellCapacity stateAlphabet stateCells *
  transcriptLeafCapacity transcriptAlphabet transcriptDepth

record BoundedCellTranscriptCapacity : Set where
  constructor bounded-cell-transcript-capacity
  field
    protectedCount : Nat
    jointCount : Nat

    stateAlphabet : Nat
    stateCells : Nat
    transcriptAlphabet : Nat
    transcriptDepth : Nat

    protectedInjectsIntoJointCount : protectedCount ≤ jointCount
    jointBoundedByCellTranscriptProduct :
      jointCount ≤
        combinedStateTranscriptCapacity
          stateAlphabet stateCells transcriptAlphabet transcriptDepth

open BoundedCellTranscriptCapacity public

protectedBoundedByCellTranscriptCapacity :
  (bounded : BoundedCellTranscriptCapacity) →
  protectedCount bounded ≤
    combinedStateTranscriptCapacity
      (stateAlphabet bounded)
      (stateCells bounded)
      (transcriptAlphabet bounded)
      (transcriptDepth bounded)
protectedBoundedByCellTranscriptCapacity bounded =
  NatP.≤-trans
    (protectedInjectsIntoJointCount bounded)
    (jointBoundedByCellTranscriptProduct bounded)

------------------------------------------------------------------------
-- Composition adapter from the generic state x transcript theorem.
------------------------------------------------------------------------

fromStateTranscriptCapacity :
  (generic : Capacity.FiniteStateTranscriptCapacity) →
  (stateAlphabet stateCells transcriptAlphabet transcriptDepth : Nat) →
  Capacity.stateCount generic ≤ stateCellCapacity stateAlphabet stateCells →
  Capacity.transcriptCount generic ≤
    transcriptLeafCapacity transcriptAlphabet transcriptDepth →
  Capacity.protectedCount generic ≤
    combinedStateTranscriptCapacity
      stateAlphabet stateCells transcriptAlphabet transcriptDepth
fromStateTranscriptCapacity
  generic stateAlphabet stateCells transcriptAlphabet transcriptDepth
  stateBound transcriptBound =
  NatP.≤-trans
    (Capacity.protectedCapacityProductBound generic)
    (NatP.*-mono-≤ stateBound transcriptBound)

------------------------------------------------------------------------
-- Exact finite regressions: one bit per state/transcript coordinate.
------------------------------------------------------------------------

binaryStateTwoCellsCapacity : stateCellCapacity 2 2 ≡ 4
binaryStateTwoCellsCapacity = refl
  where open import Agda.Builtin.Equality using (_≡_; refl)

binaryTranscriptThreeStepsCapacity : transcriptLeafCapacity 2 3 ≡ 8
binaryTranscriptThreeStepsCapacity = refl
  where open import Agda.Builtin.Equality using (_≡_; refl)

binaryTwoByThreeCombinedCapacity :
  combinedStateTranscriptCapacity 2 2 2 3 ≡ 32
binaryTwoByThreeCombinedCapacity = refl
  where open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY
--
-- A concrete ML-KEM instantiation must still prove:
--   1. which cells constitute the sufficient maintained state;
--   2. the cardinality of each cell alphabet;
--   3. the maximum outcome alphabet of one readout/query step;
--   4. the maximum transcript depth under the considered algorithm class;
--   5. that protected recovery factors through that state/transcript pair.
--
-- The theorem then turns those exact finite facts into a protected-capacity
-- bound without introducing entropy or asymptotics.
------------------------------------------------------------------------
