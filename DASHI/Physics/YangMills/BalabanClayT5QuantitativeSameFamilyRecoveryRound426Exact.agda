{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5QuantitativeSameFamilyRecoveryRound426Exact where

------------------------------------------------------------------------
-- ROUND426 / QUANTITATIVE T5 CLOSURE -> SELECTED SAME-FAMILY CONTINUUM OWNER
--
-- The mature quantitative continuum input already fixes:
--
--   * the literal diagonal physical measure sequence;
--   * its selected continuum target;
--   * complete finite-family reflected-Gram convergence;
--   * the SAME Gram measure presentation;
--   * continuum Euclidean/symmetry/tempered/regular/cluster predicates.
--
-- R426 compiles that one object into the preferred SelectedFiniteToContinuumOS
-- carrier and then into R425's pre-gap SameFamilyContinuumRecovery.
--
-- Consequently P2 expectation convergence and continuum OS reconstruction do
-- not require independently chosen continuum measures once these quantitative
-- inputs are inhabited.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit
import DASHI.Physics.YangMills.BalabanClayT5SelectedSequentialConvergenceExact as Sequential
import DASHI.Physics.YangMills.BalabanClayT5SelectedContinuumOSExact as Selected
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5OSGramTopologyExact as OS
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5QuantitativeTailMomentCompactnessExact as Quant
import DASHI.Physics.YangMills.BalabanClayT5QuantitativeContinuumClosureCompilerExact as Closure
import DASHI.Physics.YangMills.BalabanClayT5SameFamilyContinuumRecoveryRound425Exact as R425

selectedSequentialConvergence :
  ∀ {Measure Observable Scalar Marginal Schwinger}
    (inputs :
      Closure.PhysicalContinuumClosureAnalyticInputs
        Measure Observable Scalar Marginal Schwinger) →
  Sequential.SequentialConvergence Measure
selectedSequentialConvergence inputs = record
  { Sequential.SequentialConvergence.Converges =
      Limit.Converges (Closure.measureLimit inputs)
  }

selectedContinuumClosure :
  ∀ {Measure Observable Scalar Marginal Schwinger} →
  Closure.PhysicalContinuumClosureAnalyticInputs
    Measure Observable Scalar Marginal Schwinger →
  Selected.SelectedFiniteToContinuumOS Measure Schwinger
selectedContinuumClosure inputs = record
  { Selected.SelectedFiniteToContinuumOS.finiteMeasures =
      T5.diagonalMeasure
        (Quant.expectationData (Closure.quantitative inputs))
  ; Selected.SelectedFiniteToContinuumOS.continuumMeasure =
      T5.continuumMeasure
        (T5.thermodynamic
          (Quant.expectationData (Closure.quantitative inputs)))
  ; Selected.SelectedFiniteToContinuumOS.schwinger =
      Closure.schwingerMap inputs
  ; Selected.SelectedFiniteToContinuumOS.convergence =
      selectedSequentialConvergence inputs
  ; Selected.SelectedFiniteToContinuumOS.continuumIsSelectedLimit =
      Closure.diagonalConvergesToContinuum inputs
  ; Selected.SelectedFiniteToContinuumOS.Normalized =
      Closure.Normalized inputs
  ; Selected.SelectedFiniteToContinuumOS.Positive =
      Closure.Positive inputs
  ; Selected.SelectedFiniteToContinuumOS.GaugeInvariant =
      Closure.GaugeInvariant inputs
  ; Selected.SelectedFiniteToContinuumOS.ReflectionPositiveMeasure =
      OS.GramReflectionPositive
        (Gram.physicalMeasureTopologyControlsOSGram
          (Quant.osGramData (Closure.quantitative inputs)))
  ; Selected.SelectedFiniteToContinuumOS.EuclideanCovariant =
      Closure.EuclideanCovariant inputs
  ; Selected.SelectedFiniteToContinuumOS.ReflectionPositive =
      Closure.ReflectionPositive inputs
  ; Selected.SelectedFiniteToContinuumOS.Symmetric =
      Closure.Symmetric inputs
  ; Selected.SelectedFiniteToContinuumOS.Tempered =
      Closure.Tempered inputs
  ; Selected.SelectedFiniteToContinuumOS.Regular =
      Closure.Regular inputs
  ; Selected.SelectedFiniteToContinuumOS.Clustered =
      Closure.Clustered inputs
  ; Selected.SelectedFiniteToContinuumOS.continuumNormalized =
      Limit.continuumNormalized
        (Closure.compileFiniteToContinuumOSClosure inputs)
  ; Selected.SelectedFiniteToContinuumOS.continuumPositive =
      Limit.continuumPositive
        (Closure.compileFiniteToContinuumOSClosure inputs)
  ; Selected.SelectedFiniteToContinuumOS.continuumGaugeInvariant =
      Limit.continuumGaugeInvariant
        (Closure.compileFiniteToContinuumOSClosure inputs)
  ; Selected.SelectedFiniteToContinuumOS.continuumReflectionPositiveMeasure =
      Closure.physicalContinuumGramReflectionPositive inputs
  ; Selected.SelectedFiniteToContinuumOS.continuumEuclideanCovariant =
      Closure.continuumEuclideanCovariant inputs
  ; Selected.SelectedFiniteToContinuumOS.continuumReflectionPositive =
      Closure.gramReflectionImpliesSchwingerReflection inputs
        (T5.continuumMeasure
          (T5.thermodynamic
            (Quant.expectationData (Closure.quantitative inputs))))
        (Closure.physicalContinuumGramReflectionPositive inputs)
  ; Selected.SelectedFiniteToContinuumOS.continuumSymmetric =
      Closure.continuumSymmetric inputs
  ; Selected.SelectedFiniteToContinuumOS.continuumTempered =
      Closure.continuumTempered inputs
  ; Selected.SelectedFiniteToContinuumOS.continuumRegular =
      Closure.continuumRegular inputs
  ; Selected.SelectedFiniteToContinuumOS.continuumClustered =
      Closure.continuumClustered inputs
  }

record SelectedReconstructionAuthority
    {Measure Observable Scalar Marginal Schwinger : Set}
    (inputs :
      Closure.PhysicalContinuumClosureAnalyticInputs
        Measure Observable Scalar Marginal Schwinger)
    (Reconstructed : Set) : Set₁ where
  field
    reconstruct :
      Selected.SelectedContinuumOSAxioms
        (selectedContinuumClosure inputs) →
      Reconstructed

open SelectedReconstructionAuthority public

quantitativeSameFamilyRecovery :
  ∀ {Measure Observable Scalar Marginal Schwinger Reconstructed}
    (inputs :
      Closure.PhysicalContinuumClosureAnalyticInputs
        Measure Observable Scalar Marginal Schwinger) →
  SelectedReconstructionAuthority inputs Reconstructed →
  R425.SameFamilyContinuumRecovery
    Measure Observable Schwinger Scalar Reconstructed
quantitativeSameFamilyRecovery inputs authority = record
  { R425.SameFamilyContinuumRecovery.physicalGramData =
      Quant.osGramData (Closure.quantitative inputs)
  ; R425.SameFamilyContinuumRecovery.selectedClosure =
      selectedContinuumClosure inputs
  ; R425.SameFamilyContinuumRecovery.physicalMeasureSequenceAgrees =
      Closure.gramFiniteMeasureAgrees inputs
  ; R425.SameFamilyContinuumRecovery.physicalContinuumMeasureAgrees =
      Closure.gramContinuumMeasureAgrees inputs
  ; R425.SameFamilyContinuumRecovery.gramReflectionImpliesSelectedReflection =
      λ gramPositive →
        Closure.gramReflectionImpliesSchwingerReflection inputs
          (T5.continuumMeasure
            (T5.thermodynamic
              (Quant.expectationData (Closure.quantitative inputs))))
          gramPositive
  ; R425.SameFamilyContinuumRecovery.reconstructFromSelectedOSAxioms =
      reconstruct authority
  }

round426SelectedClosureCompilerLevel : ProofLevel
round426SelectedClosureCompilerLevel = machineChecked

round426SameFamilyRecoveryCompilerLevel : ProofLevel
round426SameFamilyRecoveryCompilerLevel = machineChecked

round426ReconstructionAuthorityLevel : ProofLevel
round426ReconstructionAuthorityLevel = standardImported

-- The remaining wide continuum work is precisely the analytic input record
-- consumed above, not an independent P2 measure plus an independent OS measure.
round426QuantitativeContinuumAnalyticInputsLevel : ProofLevel
round426QuantitativeContinuumAnalyticInputsLevel = conditional

round426SeparateContinuumMeasureForP2AndOSRequired : Bool
round426SeparateContinuumMeasureForP2AndOSRequired = false
