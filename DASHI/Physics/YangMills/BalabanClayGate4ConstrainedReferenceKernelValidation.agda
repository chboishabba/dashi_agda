module DASHI.Physics.YangMills.BalabanClayGate4ConstrainedReferenceKernelValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedReferenceKernelExact as Kernel

kernelConstructed :
  Kernel.constrainedReferenceKernelLevel ≡ machineChecked
kernelConstructed = refl

kernelNonnegative :
  Kernel.constrainedReferenceKernelNonnegativeLevel ≡ machineChecked
kernelNonnegative = refl

kernelNormalized :
  Kernel.constrainedReferenceKernelNormalizationLevel ≡ machineChecked
kernelNormalized = refl

kernelSupported :
  Kernel.constrainedReferenceKernelSupportLevel ≡ machineChecked
kernelSupported = refl

typedCoarseConstraintRemainsPhysical :
  Kernel.typedCanonicalReferenceCoarseConstraintLevel ≡ conditional
typedCoarseConstraintRemainsPhysical = refl
