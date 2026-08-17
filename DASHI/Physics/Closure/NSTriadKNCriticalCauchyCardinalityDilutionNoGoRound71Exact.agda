module DASHI.Physics.Closure.NSTriadKNCriticalCauchyCardinalityDilutionNoGoRound71Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Classical finite Cauchy--Schwarz inequality; DOI not applicable.
--
-- ROUND 71 / CARDINALITY-DILUTION FALSIFIER
--
-- The new finite-Cauchy bridge proves
--
--       mu^2 <= (# triadic atoms) * triadicConcentrationMass.
--
-- This file proves the cardinality factor is genuinely necessary.  Reuse the
-- Round71 dyadic branching block B_j: it contains recursively doubled entries,
-- each generation halves every value, and its signed sum stays exactly 1.
--
-- Define squaredMass(B)=sum a^2.  Then exactly
--
--       signedSum(B_j) = 1,
--       squaredMass(B_j) = 2^(-j).
--
-- Hence an order-one signed remainder may be distributed across exponentially
-- many atoms while the total squared concentration mass decays dyadically.
-- Finite Cauchy alone therefore cannot yield a scale-uniform concentration
-- charge.  The physical `CriticalAmplificationForcesStructuredConcentration`
-- theorem must localize to a controlled-cardinality subfibre (or exploit extra
-- coherent sign/geometry) before the propagation/funding mechanism can start.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNHHBadDyadicScalePrimitivesRound58 as Scale
import DASHI.Physics.Closure.NSTriadKNBranchingCompensatesDyadicLossRound71Exact as Branching
import DASHI.Physics.Closure.NSTriadKNScaleDependentConcentrationFundingRound70Exact as Funding
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

squaredMass : List ℚ → ℚ
squaredMass [] = 0ℚ
squaredMass (value ∷ rest) = L2.square value + squaredMass rest

squaredMassAppend : ∀ left right →
  squaredMass (Branching.appendFloors left right)
  ≡ squaredMass left + squaredMass right
squaredMassAppend [] right = solve (squaredMass right ∷ [])
squaredMassAppend (value ∷ rest) right =
  trans
    (cong (L2.square value +_) (squaredMassAppend rest right))
    (solve (L2.square value ∷ squaredMass rest ∷ squaredMass right ∷ []))

squaredMassScale : ∀ scalar values →
  squaredMass (Branching.scaleFloors scalar values)
  ≡ L2.square scalar * squaredMass values
squaredMassScale scalar [] = solve (scalar ∷ [])
squaredMassScale scalar (value ∷ rest)
  rewrite squaredMassScale scalar rest =
  solve (scalar ∷ value ∷ squaredMass rest ∷ [])

dyadicBranchSquaredMassExact : ∀ depth →
  squaredMass (Branching.dyadicBranchBlock depth)
  ≡ Scale.inverseDyadicScale depth
dyadicBranchSquaredMassExact zero = solve []
dyadicBranchSquaredMassExact (suc depth) =
  let
    previous = squaredMass (Branching.dyadicBranchBlock depth)
    halfBlock = Branching.scaleFloors Scale.half (Branching.dyadicBranchBlock depth)

    expanded :
      squaredMass (Branching.dyadicBranchBlock (suc depth))
      ≡ L2.square Scale.half * previous
        + L2.square Scale.half * previous
    expanded =
      trans
        (squaredMassAppend halfBlock halfBlock)
        (cong₂ _+_
          (squaredMassScale Scale.half (Branching.dyadicBranchBlock depth))
          (squaredMassScale Scale.half (Branching.dyadicBranchBlock depth)))
  in
  trans expanded
    (trans
      (cong
        (λ mass → L2.square Scale.half * mass
          + L2.square Scale.half * mass)
        (dyadicBranchSquaredMassExact depth))
      (solve (Scale.inverseDyadicScale depth ∷ [])))
  where
  open import Relation.Binary.PropositionalEquality using (cong₂)

dyadicBranchSignedSumExact : ∀ depth →
  Funding.sumFloors (Branching.dyadicBranchBlock depth) ≡ 1ℚ
dyadicBranchSignedSumExact = Branching.dyadicBranchBlockMassExact

round71OrderOneRemainderCanHaveDyadicallySmallSquaredMass : Bool
round71OrderOneRemainderCanHaveDyadicallySmallSquaredMass = true

round71CauchyAloneGivesUniformStructuredConcentration : Bool
round71CauchyAloneGivesUniformStructuredConcentration = false

round71OrderOneRemainderCanHaveDyadicallySmallSquaredMassIsTrue :
  round71OrderOneRemainderCanHaveDyadicallySmallSquaredMass ≡ true
round71OrderOneRemainderCanHaveDyadicallySmallSquaredMassIsTrue = refl

round71CauchyAloneGivesUniformStructuredConcentrationIsFalse :
  round71CauchyAloneGivesUniformStructuredConcentration ≡ false
round71CauchyAloneGivesUniformStructuredConcentrationIsFalse = refl
