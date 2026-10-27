{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkHolographicUpstreamTensorNoGoBoundaryExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Cross-kernel authority boundary for the inspected upstream canonical tensor.
--
-- Native Lean source on sibling PR #68 proves the exact support statement for
-- the inspected formula
--
--   T[(child0,child1),parent] != 0  =>  child0 = parent and child1 = 0.
--
-- Hence the named canonical tensor is only a parent-to-first-child isometry
-- into fixed-zero second-leg support. It is not itself a local source of the
-- k independent Schmidt bonds used by the corrected RT replacement network.
------------------------------------------------------------------------

inspectedCanonicalTensorSecondLegFixedZeroSourceWritten : Bool
inspectedCanonicalTensorSecondLegFixedZeroSourceWritten = true

inspectedCanonicalTensorOnlyParentChildIsometrySourceWritten : Bool
inspectedCanonicalTensorOnlyParentChildIsometrySourceWritten = true

canonicalTensorDoesNotSupplyCorrectedKBondNetwork : Bool
canonicalTensorDoesNotSupplyCorrectedKBondNetwork = true

upstreamTensorReplacementRequired : Bool
upstreamTensorReplacementRequired = true

noPromotionToAllPossibleTreeTensors : Bool
noPromotionToAllPossibleTreeTensors = true

statusStatement : String
statusStatement =
  "Sibling Lean proves that the inspected upstream canonical qubit tensor has nonzero support only when the second child leg is the fixed zero basis state and the first child equals the parent. This is a source-specific no-go for treating that tensor as the entangling k-bond RT producer; it is not a no-go for arbitrary tensor networks."
