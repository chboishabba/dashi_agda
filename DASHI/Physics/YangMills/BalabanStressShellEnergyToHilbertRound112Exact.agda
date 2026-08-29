{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanStressShellEnergyToHilbertRound112Exact where

------------------------------------------------------------------------
-- ROUND112: ROW-B ACTIVITY/ENTROPY SHELL BOUND -> STRESS HILBERT DATA
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteWeightedCauchyExact as Cauchy
import DASHI.Physics.YangMills.BalabanRowBActivityEntropyToShellEnergyExact as RowB
import DASHI.Physics.YangMills.BalabanMarkedSourceGeometricShellEnergyExact as Shell
import DASHI.Physics.YangMills.BalabanMarkedSourceCoefficientEnergyHilbertCompilerExact as Hilbert

record LiteralStressCoefficientShellIdentification : Set₁ where
  field
    shellData : RowB.SummableMarkedActivityEntropyShellData
    coefficientSamples : Nat → List Cauchy.WeightedPair

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
  L2.square (Hilbert.sourcePairing hilbert)
  ≤ Hilbert.sourceCoefficientEnergy hilbert * Hilbert.testHilbertEnergy hilbert
stressPairingSquaredCauchyFromShellEnergy dataSet cutoff =
  Hilbert.sourcePairingSquaredCauchy (stressFiniteHilbertData dataSet cutoff)

stressShellEnergyToHilbertCompilerLevel : ProofLevel
stressShellEnergyToHilbertCompilerLevel = machineChecked

literalStressCMP116ActivityEntropyInstantiationLevel : ProofLevel
literalStressCMP116ActivityEntropyInstantiationLevel = conditional

literalStressCoefficientEnergyIsShellPrefixLevel : ProofLevel
literalStressCoefficientEnergyIsShellPrefixLevel = conditional
