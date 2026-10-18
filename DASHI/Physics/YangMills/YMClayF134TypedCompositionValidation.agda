module DASHI.Physics.YangMills.YMClayF134TypedCompositionValidation where

import DASHI.Physics.YangMills.YMClayF134ContinuumWeldParityExact as F134
import DASHI.Physics.YangMills.YMClayPhysicalF34TypedCompositionExact as Typed

literalInputsExposeTypedF34Kernel :
  (inputs : F134.LiteralSU2F134PhysicalInputs) →
  Typed.PhysicalF34TypedKernel
literalInputsExposeTypedF34Kernel = F134.asTypedF34Kernel
