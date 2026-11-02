module DASHI.Mathematics.Complexity.Karp21VOAGradeDimensionCutSeparationExact where

------------------------------------------------------------------------
-- CONCRETE VOA PARTITION-GRADE vs KARP PARTITION/MAX CUT separation.
--
-- DASHI.Moonshine.RankOneFockPartitionGradingExact proves that rank-one
-- Fock grade 2 contains TWO partition-labelled basis elements. These
-- are partitions of integer energy 2, not witnesses to the PARTITION
-- equal-subset-sum decision language (Karp 1972).
--
-- On the SAME two-vertex positive-threshold Karp graph, the cut label
-- [true,false] passes and [true,true] fails. The Fock grade-2 dimension
-- is 2 in both cases. Thus a grade dimension, character coefficient or
-- a matching finite numerology cannot decide cut acceptance without an
-- input-sensitive, verified same-object map.
--
-- This is a *literal finite counterexample*, not a fabricated empty
-- "not a proof" type or an unsupported asymptotic complexity lower bound.
--
-- Primary sources: Kac (1998), FLM (1984/1988), Karp (1972).
-- Source owners: existing RankOneFockPartitionGradingExact and
-- Karp21SignedPartitionActualGraphYESExact (DASHI #1445).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import Data.Vec.Base as Vec
import DASHI.Moonshine.RankOneFockPartitionGradingExact as Fock
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21SignedPartitionActualGraphYESExact as Karp

-- Reuse the actual rank-one VOA Fock finite partition prefix.
fockGradeTwoHasTwoBasisVectors :
  Fock.listLength Fock.gradeTwoBasis ≡ 2
fockGradeTwoHasTwoBasisVectors = Fock.gradeTwoDimension

-- The very same signed weighted Karp graph has accepted/rejected
-- certificates at fixed 2-bit length. Nothing about the Fock grade
-- coefficient determines which Boolean labels were supplied.
fockGradeTwoKarpTwoVertexDecisionSeparation :
  (Fock.listLength Fock.gradeTwoBasis ≡ 2) ×
  (Cut.verifyWeightedMaxCut
     Karp.fixedUnitGraph
     (true Vec.∷ false Vec.∷ Vec.[]) ≡ true) ×
  (Cut.verifyWeightedMaxCut
     Karp.fixedUnitGraph
     (true Vec.∷ true Vec.∷ Vec.[]) ≡ false)
fockGradeTwoKarpTwoVertexDecisionSeparation =
  fockGradeTwoHasTwoBasisVectors , (refl , refl)
