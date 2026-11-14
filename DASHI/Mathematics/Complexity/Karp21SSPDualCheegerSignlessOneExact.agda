module DASHI.Mathematics.Complexity.Karp21SSPDualCheegerSignlessOneExact where

------------------------------------------------------------------------
-- FINITE SIGNLESS 1-LAPLACIAN OBJECTIVE ON THE EXISTING SSP TRIT.
--
-- Authors/roots: Fan Chung (1997); dual Cheeger constants of Bauer,
-- Hua and Jost (2012); Shao, Yang and Zhang (2016 preprint,
-- Science China Mathematics 2025, DOI 10.1007/s11425-024-2376-2).
--
-- For x_i in {-1,0,+1}, the elementary signless edge term is
--     I_plus(x_i,x_j) = |x_i+x_j| in Nat.
-- This is not the ordinary quadratic gap (x_i-x_j)^2 and is
-- not a general MaxCut approximation theorem.
--
-- Nonnegative Nat edge weights are REQUIRED; signed Karp weights or
-- PNF contradiction severities cannot be silently substituted.
-- We prove explicit finite outcomes and list-level additivity on
-- this carrier; dual-Cheeger degree denominators/eigenvalue
-- inequalities, spectral subgradients and algorithmic ratios remain
-- separate, unproven hypotheses.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Foundations.SSPTritCarrier as SSP
import Data.Nat.Properties as NatP

-- Exact integer absolute value table for three-valued signed inputs.
signlessOneGap :
  SSP.SSPTrit → SSP.SSPTrit → Nat
signlessOneGap SSP.sspNegOne SSP.sspNegOne = 2
signlessOneGap SSP.sspNegOne SSP.sspZero = 1
signlessOneGap SSP.sspNegOne SSP.sspPosOne = 0
signlessOneGap SSP.sspZero SSP.sspNegOne = 1
signlessOneGap SSP.sspZero SSP.sspZero = 0
signlessOneGap SSP.sspZero SSP.sspPosOne = 1
signlessOneGap SSP.sspPosOne SSP.sspNegOne = 0
signlessOneGap SSP.sspPosOne SSP.sspZero = 1
signlessOneGap SSP.sspPosOne SSP.sspPosOne = 2

signlessOneSymmetric :
  (a b : SSP.SSPTrit) →
  signlessOneGap a b ≡ signlessOneGap b a
signlessOneSymmetric SSP.sspNegOne SSP.sspNegOne = refl
signlessOneSymmetric SSP.sspNegOne SSP.sspZero = refl
signlessOneSymmetric SSP.sspNegOne SSP.sspPosOne = refl
signlessOneSymmetric SSP.sspZero SSP.sspNegOne = refl
signlessOneSymmetric SSP.sspZero SSP.sspZero = refl
signlessOneSymmetric SSP.sspZero SSP.sspPosOne = refl
signlessOneSymmetric SSP.sspPosOne SSP.sspNegOne = refl
signlessOneSymmetric SSP.sspPosOne SSP.sspZero = refl
signlessOneSymmetric SSP.sspPosOne SSP.sspPosOne = refl

signlessOneOppositeVanishes :
  signlessOneGap SSP.sspNegOne SSP.sspPosOne ≡ 0
signlessOneOppositeVanishes = refl

signlessOneSamePositiveIsTwo :
  signlessOneGap SSP.sspPosOne SSP.sspPosOne ≡ 2
signlessOneSamePositiveIsTwo = refl

signlessOneNeutralPositiveIsOne :
  signlessOneGap SSP.sspZero SSP.sspPosOne ≡ 1
signlessOneNeutralPositiveIsOne = refl

-- Crucial counterexample: the signless 1-edge term is nonzero
-- on agreeing positive spins, while ordinary quadratic gap is zero.
signlessOneIsNotOrdinaryGapAtEqualPositive :
  signlessOneGap SSP.sspPosOne SSP.sspPosOne ≡ 2
signlessOneIsNotOrdinaryGapAtEqualPositive = refl

record NonnegativeWeightedTritEdge : Set where
  constructor trit-edge
  field
    source target : SSP.SSPTrit
    magnitude : Nat

open NonnegativeWeightedTritEdge public

signlessOneEdgeScore : NonnegativeWeightedTritEdge → Nat
signlessOneEdgeScore e =
  magnitude e * signlessOneGap (source e) (target e)

signlessOneListScore : List NonnegativeWeightedTritEdge → Nat
signlessOneListScore [] = 0
signlessOneListScore (e ∷ es) =
  signlessOneEdgeScore e + signlessOneListScore es

signlessOneListAppend :
  (left right : List NonnegativeWeightedTritEdge) →
  signlessOneListScore (left ++ right) ≡
  signlessOneListScore left + signlessOneListScore right
signlessOneListAppend [] right = refl
signlessOneListAppend (e ∷ es) right =
  trans
    (cong (λ score → signlessOneEdgeScore e + score)
      (signlessOneListAppend es right))
    (sym (NatP.+-assoc
      (signlessOneEdgeScore e)
      (signlessOneListScore es)
      (signlessOneListScore right)))
