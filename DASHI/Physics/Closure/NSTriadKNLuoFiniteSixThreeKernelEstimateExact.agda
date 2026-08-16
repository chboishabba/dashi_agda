module DASHI.Physics.Closure.NSTriadKNLuoFiniteSixThreeKernelEstimateExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- DOI: 10.1007/BF02099744.
--
-- Author: Piero D'Ancona.
-- Title: "A Short Proof of Commutator Estimates".
-- DOI: 10.1007/s00041-018-9612-8.
-- Correction DOI: 10.1007/s00041-019-09724-7.
--
-- Authors: Francesca Da Lio; Tristan Rivière.
-- Title: "Three-Term Commutator Estimates and the Regularity of
-- 1/2-Harmonic Maps into Spheres".
-- DOI: 10.2140/apde.2011.4.149.
--
-- COMPILER ASSEMBLY
--
-- The expensive one-branch rational transport now lives behind
-- NSTriadKNLuoFiniteSixThreeKernelBranchBoundary.  This historical import path
-- contains only the centered two-branch assembly and publicly re-exports the
-- source carrier/branch theorem.  In particular it no longer imports the full
-- NSTriadKNRationalOrderedFiniteL2 Gram/Cauchy--Schwarz development.
--
-- No postulate or physical assumption is introduced by this split.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import DASHI.Physics.Closure.NSTriadKNLuoFiniteSixThreeKernelBranchBoundary public
import DASHI.Physics.Closure.NSTriadKNLuoFiniteEightPointSixThreeHolderExact as Holder

centeredEndpoint :
  (x y z u v : ℚ) →
  Holder.four
    * (Holder.sixtyFour * Holder.cube x * y * (z * z)
      + Holder.sixtyFour * Holder.cube x * u * (v * v))
  ≡ (Holder.four * Holder.sixtyFour)
      * Holder.cube x
      * (y * (z * z) + u * (v * v))
centeredEndpoint x y z u v
  rewrite Holder.cubeMeaning x | Holder.sixtyFourMeaning
  = solve (x ∷ y ∷ z ∷ u ∷ v ∷ [])

abstract
  centeredSixThreeKernelSixthPowerBound :
    (dataSet : FiniteSixThreeKernelData) →
    Holder.cube
      (firstBranchL2Squared dataSet + secondBranchL2Squared dataSet)
    ≤ (Holder.four * Holder.sixtyFour)
      * Holder.cube (kernelSecondMomentSquared dataSet)
      * ( Holder.lowSixthMass (firstHolder dataSet)
          * (Holder.highCubeMass (firstHolder dataSet)
            * Holder.highCubeMass (firstHolder dataSet))
        + Holder.lowSixthMass (secondHolder dataSet)
          * (Holder.highCubeMass (secondHolder dataSet)
            * Holder.highCubeMass (secondHolder dataSet)))
  centeredSixThreeKernelSixthPowerBound dataSet =
    let
      pairBound =
        Holder.cubePairBound
          (firstBranchL2Squared dataSet)
          (secondBranchL2Squared dataSet)
          (firstBranchNonnegative dataSet)
          (secondBranchNonnegative dataSet)

      first = branchCubeBound
        (firstHolder dataSet)
        (kernelSecondMomentSquared dataSet)
        (firstBranchL2Squared dataSet)
        (kernelSecondMomentSquaredNonnegative dataSet)
        (firstBranchNonnegative dataSet)
        (firstKernelBound dataSet)

      second = branchCubeBound
        (secondHolder dataSet)
        (kernelSecondMomentSquared dataSet)
        (secondBranchL2Squared dataSet)
        (kernelSecondMomentSquaredNonnegative dataSet)
        (secondBranchNonnegative dataSet)
        (secondKernelBound dataSet)

      summed = ℚₚ.+-mono-≤ first second

      scaled = Holder.scaleBound
        Holder.four _ _ Holder.fourNonnegative summed

      endpoint = centeredEndpoint
        (kernelSecondMomentSquared dataSet)
        (Holder.lowSixthMass (firstHolder dataSet))
        (Holder.highCubeMass (firstHolder dataSet))
        (Holder.lowSixthMass (secondHolder dataSet))
        (Holder.highCubeMass (secondHolder dataSet))
    in
    ℚₚ.≤-trans
      pairBound
      (subst
        (λ upper →
          Holder.four
            * (Holder.cube (firstBranchL2Squared dataSet)
              + Holder.cube (secondBranchL2Squared dataSet))
          ≤ upper)
        endpoint
        scaled)
