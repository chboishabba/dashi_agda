module DASHI.Physics.Closure.NSTriadKNComLiteralSameAdjacentFibreRound55Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Issai Schur. Classical row/column test; no DOI assigned to the
-- historical theorem used here.
--
-- DASHI CONTRIBUTION
--
-- The Com route is a squared whole-output-fibre estimate.  Round 54 connected
-- the finite Schur theorem to the literal physicalOutputFiber enumeration.
-- Here the two physical analytic constants are assembled without changing
-- their meaning:
--
--   same shell       <= 17/64,
--   each adjacent    <= 65/512,
--
-- hence the bandwidth-one squared row coefficient is exactly
--   17/64 + 2(65/512) = 133/256.
--
-- The theorem is deliberately formulated on literal whole-fibre masses; no
-- incidence cardinality or square-root reinterpretation is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _≤_; _/_)
import Data.Integer.Base as Int
open import Data.Rational.Tactic.RingSolver using (solve)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNComSameAdjacentActiveRound47Exact as Active
import DASHI.Physics.Closure.NSTriadKNComThreeChannelRowMassRound48Exact as Row

same adjacent target : ℚ
same = Int.+ 17 / 64
adjacent = Int.+ 65 / 512
target = Int.+ 133 / 256

targetArithmetic : same + adjacent + adjacent ≡ target
targetArithmetic = solve []

record LiteralWholeFibreMasses : Set where
  field
    sameMass forwardAdjacentMass reverseAdjacentMass : ℚ
    sameMassBelow : sameMass ≤ same
    forwardAdjacentMassBelow : forwardAdjacentMass ≤ adjacent
    reverseAdjacentMassBelow : reverseAdjacentMass ≤ adjacent

open LiteralWholeFibreMasses public

wholeBandwidthOneMass : LiteralWholeFibreMasses → ℚ
wholeBandwidthOneMass masses =
  sameMass masses + forwardAdjacentMass masses + reverseAdjacentMass masses

wholeBandwidthOneMassBelow133Over256 :
  (masses : LiteralWholeFibreMasses) →
  wholeBandwidthOneMass masses ≤ target
wholeBandwidthOneMassBelow133Over256 masses =
  let
    summed =
      ℚP.+-mono-≤
        (ℚP.+-mono-≤
          (sameMassBelow masses)
          (forwardAdjacentMassBelow masses))
        (reverseAdjacentMassBelow masses)
  in
  Relation.Binary.PropositionalEquality.subst
    (λ upper → wholeBandwidthOneMass masses ≤ upper)
    targetArithmetic
    summed

targetIsMatureThreeChannelTarget : target ≡ Row.threeChannelTarget
targetIsMatureThreeChannelTarget = solve []

sameTargetMatchesRound47 : same ≡ Active.sameShellTarget
sameTargetMatchesRound47 = solve []

adjacentTargetMatchesRound47 : adjacent ≡ Active.adjacentShellTarget
adjacentTargetMatchesRound47 = solve []

comWholeBlockConstantAssembled : Bool
comWholeBlockConstantAssembled = true

comWholeBlockConstantAssembledIsTrue :
  comWholeBlockConstantAssembled ≡ true
comWholeBlockConstantAssembledIsTrue = refl
