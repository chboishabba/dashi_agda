{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkHolographicTreeReplacementContractBoundaryExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Cross-kernel boundary for the exact corrected-tree replacement contract.
--
-- Sibling Lean PR #68 defines `CorrectedTreeReplacement k`.  Once an actual
-- tree/tensor construction supplies:
--   1. an equivalence from its boundary carrier to the corrected bipartite
--      carrier,
--   2. equality of its contracted density with the corrected coherent density,
--   3. an actual selected cut with exactly k independent bonds,
--   4. same-object identification of its entropy and cut entropy,
-- the already-proved corrected network RT theorem compiles immediately to the
-- actual construction.
------------------------------------------------------------------------

sourceReplacementContractOwned : Bool
sourceReplacementContractOwned = true

actualTreeContractionIdentificationStillExternal : Bool
actualTreeContractionIdentificationStillExternal = true

actualSubtreeCutIdentificationStillExternal : Bool
actualSubtreeCutIdentificationStillExternal = true

noFurtherRTEntropyAlgebraRequired : Bool
noFurtherRTEntropyAlgebraRequired = true

currentUpstreamDefinitionsDoNotInstantiateContract : Bool
currentUpstreamDefinitionsDoNotInstantiateContract = true

statusStatement : String
statusStatement =
  "The remaining RT source seam is exactly construction of the corrected-tree replacement contract for an actual tree/subtree. Once same-object contraction and cut identifications are supplied, no additional entropy or minimal-cut algebra remains."
