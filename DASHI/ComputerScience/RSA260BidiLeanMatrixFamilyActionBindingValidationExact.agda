module DASHI.ComputerScience.RSA260BidiLeanMatrixFamilyActionBindingValidationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.ComputerScience.RSA260BidiLeanMatrixFamilyActionBindingExact as Owner

------------------------------------------------------------------------
-- RED/GREEN surface for the matrix-family action donor.
------------------------------------------------------------------------

boundary : Owner.LeanMatrixFamilyActionBindingBoundary
boundary = Owner.canonicalLeanMatrixFamilyActionBindingBoundary

sourceWritten : Bool
sourceWritten = Owner.leanMatrixFamilyActionSourceWritten boundary

perLayerLinearityWritten : Bool
perLayerLinearityWritten = Owner.fixedLeftMatrixLayerLinearityWritten boundary

familyAssemblyWritten : Bool
familyAssemblyWritten = Owner.matrixCoefficientFamilyActionWritten boundary

runtimeBindingPaid : Bool
runtimeBindingPaid = Owner.syntheticKrylovLayerMatricesBound boundary

formalKernelPaid : Bool
formalKernelPaid = Owner.formalJointKernelEqualityPaid boundary
