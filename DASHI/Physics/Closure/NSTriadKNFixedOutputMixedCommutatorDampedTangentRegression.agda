module DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as Cut

fixedOutputDampedTangentDecompositionRequired :
  Cut.fixedOutputDampedTangentDecompositionClosed ≡ true
fixedOutputDampedTangentDecompositionRequired = refl

fixedOutputCommutatorDynamicResidualRequired :
  Cut.fixedOutputCommutatorDynamicResidualIdentified ≡ true
fixedOutputCommutatorDynamicResidualRequired = refl

coherentDampingNotManufacturedRequired :
  Cut.cellwiseDampingLowerBoundPaysCoherentFixedOutput ≡ false
coherentDampingNotManufacturedRequired = refl

signedCovarianceResidualRequired :
  Cut.remainingD1LeafIsSignedCoherentCovarianceOrEquivalent ≡ true
signedCovarianceResidualRequired = refl

d1StillOpenRequired :
  Cut.d1QuantitativePaymentClosed ≡ false
d1StillOpenRequired = refl
