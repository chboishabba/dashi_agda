module DASHI.Physics.YangMills.BalabanFiniteProbabilityPartitionDisintegrationValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteProbabilityPartitionDisintegrationExact as Partition

conditionalKernelClosed :
  Partition.finitePartitionConditionalKernelLevel ≡ machineChecked
conditionalKernelClosed = refl

kernelNormalizationClosed :
  Partition.finitePartitionKernelNormalizationLevel ≡ machineChecked
kernelNormalizationClosed = refl

disintegrationClosed :
  Partition.finitePartitionDisintegrationLevel ≡ machineChecked
disintegrationClosed = refl

positiveCoarseWitnessCompilerClosed :
  Partition.finiteCoarseFibrePositiveWitnessCompilerLevel ≡ machineChecked
positiveCoarseWitnessCompilerClosed = refl
