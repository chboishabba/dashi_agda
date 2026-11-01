module DASHI.Geometry.FiniteCausalDiamondClosed where

import DASHI.Geometry.FiniteCausalDiamond as Diamond
open import DASHI.Unified.GRQuantumProofTerms

------------------------------------------------------------------------
-- Inhabited closure companion for the exact finite causal diamond surface.

finiteCausalDiamondClosed :
  ChainAntichainLorentzClosed Diamond.finiteCausalDiamondProof
finiteCausalDiamondClosed =
  record
    { finiteSpeedConeProof = Diamond.nullImpliesCausalEdge
    ; signatureUniqueProof = Diamond.finiteSignatureUnique
    }
