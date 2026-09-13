module DASHI.Physics.Materials.FangDainingInverseDesignReferenceKernelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Materials.FangDainingInverseDesignSourceReplayExact as F

record FangInverseDesignReferenceKernel : Set where
  constructor fang-inverse-design-reference-kernel
  field
    sourceReference : String
    designMethod : String
    prescribedObjects : String
    experimentalValidation : String
    negativeGroupVelocityVerified : Bool
    executableInverseDesignPaid : Bool
    blockingCoordinate : String

open FangInverseDesignReferenceKernel public

fangInverseDesignReferenceKernel : FangInverseDesignReferenceKernel
fangInverseDesignReferenceKernel = fang-inverse-design-reference-kernel
  (F.FangInverseDesignSourceReplay.sourceReference F.sourceExactFangInverseDesignReplay)
  (F.FangInverseDesignSourceReplay.designMethod F.sourceExactFangInverseDesignReplay)
  (F.FangInverseDesignSourceReplay.prescribedObjects F.sourceExactFangInverseDesignReplay)
  (F.FangInverseDesignSourceReplay.experimentalValidation F.sourceExactFangInverseDesignReplay)
  true
  false
  "complete energy functional, unit-cell geometry, material constants and computed/experimental band arrays"

sourceObjectiveProjectionExecutable : Bool
sourceObjectiveProjectionExecutable = true

inverseDesignAlgorithmExecutable : Bool
inverseDesignAlgorithmExecutable = false
