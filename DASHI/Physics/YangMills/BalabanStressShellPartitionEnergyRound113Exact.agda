{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanStressShellPartitionEnergyRound113Exact where

------------------------------------------------------------------------
-- ROUND113: PER-SHELL COEFFICIENT IDENTIFICATION -> GLOBAL ENERGY PREFIX
--
-- Round112 asked for a global equality between weighted coefficient energy and
-- the Row-B shell-energy prefix.  That equality is finite bookkeeping once the
-- actual stress coefficients are partitioned into shell blocks.  This file
-- proves the bookkeeping directly.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNLuoFiniteWeightedCauchyExact as Cauchy
import DASHI.Physics.YangMills.BalabanRowBActivityEntropyToShellEnergyExact as RowB
import DASHI.Physics.YangMills.BalabanMarkedSourceGeometricShellEnergyExact as Shell
import DASHI.Physics.YangMills.BalabanStressShellEnergyToHilbertRound112Exact as R112

appendSamples : List Cauchy.WeightedPair → List Cauchy.WeightedPair → List Cauchy.WeightedPair
appendSamples [] right = right
appendSamples (sample ∷ left) right = sample ∷ appendSamples left right

leftEnergyAppend : ∀ left right →
  Cauchy.leftEnergy (appendSamples left right)
  ≡ Cauchy.leftEnergy left + Cauchy.leftEnergy right
leftEnergyAppend [] right = refl
leftEnergyAppend (sample ∷ left) right
  rewrite leftEnergyAppend left right = refl

record LiteralStressShellPartition : Set₁ where
  field
    shellData : RowB.SummableMarkedActivityEntropyShellData
    shellSamples : Nat → List Cauchy.WeightedPair

    -- Only physical bookkeeping left here: each geometric shell energy is the
    -- weighted coefficient energy of the literal CMP116 stress coefficients in
    -- that shell.
    shellEnergyIsCoefficientEnergy : ∀ depth →
      Shell.shellEnergy (RowB.asGeometricMarkedShellEnergy shellData) depth
      ≡ Cauchy.leftEnergy (shellSamples depth)
open LiteralStressShellPartition public

coefficientSamplesThrough :
  LiteralStressShellPartition → Nat → List Cauchy.WeightedPair
coefficientSamplesThrough dataSet zero = shellSamples dataSet zero
coefficientSamplesThrough dataSet (suc cutoff) =
  appendSamples
    (shellSamples dataSet (suc cutoff))
    (coefficientSamplesThrough dataSet cutoff)

coefficientPrefixEnergyIsShellPrefix :
  (dataSet : LiteralStressShellPartition) → ∀ cutoff →
  Cauchy.leftEnergy (coefficientSamplesThrough dataSet cutoff)
  ≡ Shell.shellEnergyPrefix
      (RowB.asGeometricMarkedShellEnergy (shellData dataSet)) cutoff
coefficientPrefixEnergyIsShellPrefix dataSet zero =
  let perShell = shellEnergyIsCoefficientEnergy dataSet zero
  in
  trans refl (Relation.Binary.PropositionalEquality.sym perShell)
coefficientPrefixEnergyIsShellPrefix dataSet (suc cutoff) =
  let
    current = shellSamples dataSet (suc cutoff)
    previous = coefficientSamplesThrough dataSet cutoff
    appendEnergy = leftEnergyAppend current previous
    currentEnergy = shellEnergyIsCoefficientEnergy dataSet (suc cutoff)
    previousEnergy = coefficientPrefixEnergyIsShellPrefix dataSet cutoff
  in
  trans appendEnergy
    (trans
      (cong (λ x → x + Cauchy.leftEnergy previous)
        (Relation.Binary.PropositionalEquality.sym currentEnergy))
      (cong
        (λ x →
          Shell.shellEnergy
            (RowB.asGeometricMarkedShellEnergy (shellData dataSet))
            (suc cutoff) + x)
        previousEnergy))

asRound112StressCoefficientShellIdentification :
  LiteralStressShellPartition → R112.LiteralStressCoefficientShellIdentification
asRound112StressCoefficientShellIdentification dataSet = record
  { R112.LiteralStressCoefficientShellIdentification.shellData = shellData dataSet
  ; R112.LiteralStressCoefficientShellIdentification.coefficientSamples =
      coefficientSamplesThrough dataSet
  ; R112.LiteralStressCoefficientShellIdentification.coefficientEnergyIsShellPrefix =
      coefficientPrefixEnergyIsShellPrefix dataSet
  }

stressShellPartitionEnergyCompilerLevel : ProofLevel
stressShellPartitionEnergyCompilerLevel = machineChecked

-- The global energy-prefix equality is no longer a physical theorem.  The live
-- source task is only the per-shell identification of the literal differentiated
-- CMP116 stress coefficients with the Row-B shell-energy decomposition.
literalStressPerShellCoefficientIdentificationLevel : ProofLevel
literalStressPerShellCoefficientIdentificationLevel = conditional
