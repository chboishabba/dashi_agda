{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanStressShellEnergyToHilbertRound112Exact where

------------------------------------------------------------------------
-- ROUND112: ROW-B ACTIVITY/ENTROPY SHELL BOUND -> STRESS HILBERT DATA
--
-- The repository already proves:
--
--   differentiated activity decay + shell entropy + (a e < 1)
--     -> GeometricMarkedShellEnergy
--     -> cutoff-uniform shell-energy prefix bound.
--
-- It also already proves weighted Cauchy--Schwarz for a finite marked source.
-- This file removes the remaining bookkeeping between those two owners.  Once
-- the actual differentiated stress coefficients are identified so that their
-- finite weighted coefficient energy is exactly the corresponding shell prefix,
-- the Row-B bound supplies the coefficient cap required by the Hilbert compiler.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNLuoFiniteWeightedCauchyExact as Cauchy
import DASHI.Physics.YangMills.BalabanRowBActivityEntropyToShellEnergyExact as RowB
import DASHI.Physics.YangMills.BalabanMarkedSourceGeometricShellEnergyExact as Shell
import DASHI.Physics.YangMills.BalabanMarkedSourceCoefficientEnergyHilbertCompilerExact as Hilbert

record LiteralStressCoefficientShellIdentification : Set₁ where
  field
    shellData : RowB.SummableMarkedActivityEntropyShellData
    coefficientSamples : Nat → List Cauchy.WeightedPair

    -- Same physical differentiated stress coefficients, merely regrouped by
    -- geometric shell depth.
    coefficientEnergyIsShellPrefix : ∀ cutoff →
      Cauchy.leftEnergy (coefficientSamples cutoff)
      ≡ Shell.shellEnergyPrefix
          (RowB.asGeometricMarkedShellEnergy shellData) cutoff
open LiteralStressCoefficientShellIdentification public

stressCoefficientEnergyUniformBound :
  (dataSet : LiteralStressCoefficientShellIdentification) → ∀ cutoff →
  Cauchy.leftEnergy (coefficientSamples dataSet cutoff)
  ≤ RowB.combinedBaseEnergy (RowB.sourceData (shellData dataSet))
      * RowB.geometricBound (shellData dataSet)
stressCoefficientEnergyUniformBound dataSet cutoff =
  subst
    (λ selected → selected
      ≤ RowB.combinedBaseEnergy (RowB.sourceData (shellData dataSet))
          * RowB.geometricBound (shellData dataSet))
    (coefficientEnergyIsShellPrefix dataSet cutoff)
    (RowB.activityEntropyPrefixUniformBound (shellData dataSet) cutoff)

stressFiniteHilbertData :
  (dataSet : LiteralStressCoefficientShellIdentification) →
  Nat → Hilbert.FiniteMarkedSourceHilbertData
stressFiniteHilbertData dataSet cutoff = record
  { Hilbert.FiniteMarkedSourceHilbertData.samples = coefficientSamples dataSet cutoff
  ; Hilbert.FiniteMarkedSourceHilbertData.coefficientEnergyCap =
      RowB.combinedBaseEnergy (RowB.sourceData (shellData dataSet))
        * RowB.geometricBound (shellData dataSet)
  ; Hilbert.FiniteMarkedSourceHilbertData.coefficientEnergyBound =
      stressCoefficientEnergyUniformBound dataSet cutoff
  }

stressPairingSquaredCauchyFromShellEnergy :
  (dataSet : LiteralStressCoefficientShellIdentification) →
  ∀ cutoff →
  let hilbert = stressFiniteHilbertData dataSet cutoff
  in
  Hilbert.L2.square (Hilbert.sourcePairing hilbert)
  ≤ Hilbert.sourceCoefficientEnergy hilbert * Hilbert.testHilbertEnergy hilbert
stressPairingSquaredCauchyFromShellEnergy dataSet cutoff =
  Hilbert.sourcePairingSquaredCauchy (stressFiniteHilbertData dataSet cutoff)

stressShellEnergyToHilbertCompilerLevel : ProofLevel
stressShellEnergyToHilbertCompilerLevel = machineChecked

-- Remaining physical source bindings: instantiate Row-B's differentiated
-- activity/entropy data on the literal CMP116 stress coordinate, prove the
-- strict combined ratio gap, and identify the weighted coefficient energy with
-- the corresponding geometric shell prefix.
literalStressCMP116ActivityEntropyInstantiationLevel : ProofLevel
literalStressCMP116ActivityEntropyInstantiationLevel = conditional

literalStressCoefficientEnergyIsShellPrefixLevel : ProofLevel
literalStressCoefficientEnergyIsShellPrefixLevel = conditional
