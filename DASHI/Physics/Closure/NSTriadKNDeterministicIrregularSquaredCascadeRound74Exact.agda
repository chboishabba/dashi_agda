module DASHI.Physics.Closure.NSTriadKNDeterministicIrregularSquaredCascadeRound74Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Authors: Jean-Pierre Kahane; Jacques Peyriere.
-- Title: "Sur certaines martingales de Benoit Mandelbrot".
-- Advances in Mathematics 22 (1976), 131--145.
-- DOI: 10.1016/0001-8708(76)90151-1.
--
-- ROUND74 / DETERMINISTIC IRREGULAR CASCADE SKELETON
--
-- Kahane--Peyriere studies multiplicative random cascades.  The Navier--Stokes
-- funding problem here is finite and deterministic, so none of the
-- measure-theoretic/random machinery is imported.  We retain only the exact
-- arithmetic invariant suggested by that theory.
--
-- If one parent has amplitude mu and child amplitudes
--
--      r_1 mu, ..., r_m mu,
--
-- then the total squared-amplification floor of the children is EXACTLY
--
--      mu^2 * (sum_i r_i^2).
--
-- Therefore the irregular critical surface is not a fixed branching number:
--
--      sum_i r_i^2 = 1.
--
-- The four children with r_i=1/2 from Round73 are only the homogeneous special
-- case.  Different nodes may have different arities and different losses.
--
-- This module proves the node law and its finite-generation sum exactly.  It
-- does NOT claim Navier--Stokes supplies such children, nor that formal child
-- names have additive physical charge; those remain the physical propagation
-- theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNBranchingCompensatesDyadicLossRound71Exact as Branch
import DASHI.Physics.Closure.NSTriadKNCriticalCauchyCardinalityDilutionNoGoRound71Exact as Mass
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

irregularChildAmplitudes : ℚ → List ℚ → List ℚ
irregularChildAmplitudes parentAmplitude lossWeights =
  Branch.scaleFloors parentAmplitude lossWeights

irregularChildSquaredMassExact : ∀ parentAmplitude lossWeights →
  Mass.squaredMass (irregularChildAmplitudes parentAmplitude lossWeights)
  ≡ L2.square parentAmplitude * Mass.squaredMass lossWeights
irregularChildSquaredMassExact parentAmplitude lossWeights =
  Mass.squaredMassScale parentAmplitude lossWeights

record CriticalSquaredPropagationRow : Set where
  constructor critical-row
  field
    parentAmplitude : ℚ
    childLossWeights : List ℚ
    squaredLossMassCritical : Mass.squaredMass childLossWeights ≡ 1ℚ

open CriticalSquaredPropagationRow public

criticalRowPreservesSquaredFloor :
  (row : CriticalSquaredPropagationRow) →
  Mass.squaredMass
    (irregularChildAmplitudes
      (parentAmplitude row)
      (childLossWeights row))
  ≡ L2.square (parentAmplitude row)
criticalRowPreservesSquaredFloor row =
  trans
    (irregularChildSquaredMassExact
      (parentAmplitude row) (childLossWeights row))
    (trans
      (cong (L2.square (parentAmplitude row) *_)
        (squaredLossMassCritical row))
      (solve (parentAmplitude row ∷ [])))

criticalParentMass : List CriticalSquaredPropagationRow → ℚ
criticalParentMass [] = 0ℚ
criticalParentMass (row ∷ rows) =
  L2.square (parentAmplitude row) + criticalParentMass rows

criticalChildMass : List CriticalSquaredPropagationRow → ℚ
criticalChildMass [] = 0ℚ
criticalChildMass (row ∷ rows) =
  Mass.squaredMass
    (irregularChildAmplitudes
      (parentAmplitude row)
      (childLossWeights row))
  + criticalChildMass rows

criticalIrregularGenerationPreservesSquaredFloor :
  ∀ rows → criticalChildMass rows ≡ criticalParentMass rows
criticalIrregularGenerationPreservesSquaredFloor [] = refl
criticalIrregularGenerationPreservesSquaredFloor (row ∷ rows) =
  trans
    (cong
      (λ first → first + criticalChildMass rows)
      (criticalRowPreservesSquaredFloor row))
    (cong
      (L2.square (parentAmplitude row) +_)
      (criticalIrregularGenerationPreservesSquaredFloor rows))

record SupercriticalSquaredPropagationRow : Set where
  constructor supercritical-row
  field
    parentAmplitude : ℚ
    childLossWeights : List ℚ
    excessSquaredMass : ℚ
    squaredLossMassExact :
      Mass.squaredMass childLossWeights ≡ 1ℚ + excessSquaredMass

open SupercriticalSquaredPropagationRow
  renaming
    ( parentAmplitude to superParentAmplitude
    ; childLossWeights to superChildLossWeights
    ; excessSquaredMass to superExcessSquaredMass
    ; squaredLossMassExact to superSquaredLossMassExact
    ) public

supercriticalRowExcessExact :
  (row : SupercriticalSquaredPropagationRow) →
  Mass.squaredMass
    (irregularChildAmplitudes
      (superParentAmplitude row)
      (superChildLossWeights row))
  ≡
  L2.square (superParentAmplitude row)
  + L2.square (superParentAmplitude row) * superExcessSquaredMass row
supercriticalRowExcessExact row =
  trans
    (irregularChildSquaredMassExact
      (superParentAmplitude row) (superChildLossWeights row))
    (trans
      (cong (L2.square (superParentAmplitude row) *_)
        (superSquaredLossMassExact row))
      (solve
        (superParentAmplitude row ∷ superExcessSquaredMass row ∷ [])))

round74IrregularCriticalInvariantIsSumSquaredLoss : Bool
round74IrregularCriticalInvariantIsSumSquaredLoss = true

round74CriticalIrregularGenerationMassPreserved : Bool
round74CriticalIrregularGenerationMassPreserved = true

round74PhysicalIrregularNSDescendantRowsConstructed : Bool
round74PhysicalIrregularNSDescendantRowsConstructed = false

round74CriticalIrregularGenerationMassPreservedIsTrue :
  round74CriticalIrregularGenerationMassPreserved ≡ true
round74CriticalIrregularGenerationMassPreservedIsTrue = refl

round74PhysicalIrregularNSDescendantRowsConstructedIsFalse :
  round74PhysicalIrregularNSDescendantRowsConstructed ≡ false
round74PhysicalIrregularNSDescendantRowsConstructedIsFalse = refl
