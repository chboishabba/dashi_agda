module DASHI.Core.GeneralizedRoleFormalLensBridge where

open import Agda.Builtin.String using (String)
open import DASHI.Core.FormalLensVocabularyCore
open import DASHI.Core.ProofLens

-- The compact operational proof-lens vocabulary embeds into DASHI's broader
-- formal-lens catalogue.  Named lenses remain explicit rather than being
-- silently identified with nearby mathematical families.
proofLensKind : ProofLens → FormalLensKind
proofLensKind waveLens        = NamedFormalLensKind "Wave"
proofLensKind btBraidLens     = NamedFormalLensKind "BalancedTernaryBraid"
proofLensKind spectralLens    = SpectralSequence
proofLensKind graphLens       = Graph
proofLensKind categoryLens    = Category
proofLensKind hamiltonianLens = Hamiltonian
proofLensKind statisticalLens = Statistical
proofLensKind pnfLens         = Provenance
proofLensKind historicalLens  = NamedFormalLensKind "Historical"
proofLensKind otherLens       = NamedFormalLensKind "OtherRoleProofLens"

proofLensFamily : ProofLens → FormalLensFamily
proofLensFamily lens = familyOf (proofLensKind lens)
