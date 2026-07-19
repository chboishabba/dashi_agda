module DASHI.Information.PNFSpectralGeometryTests where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import DASHI.Information.PNFSpectralGeometry

coordinate-role-is-discrete : atomCodeRole ≡ coordinateIdentifier
coordinate-role-is-discrete = refl

first-atom-code : atomCode (atom-coordinate zero) ≡ zero
first-atom-code = refl

second-mode-code : modeCode (mode-coordinate (suc zero)) ≡ suc zero
second-mode-code = refl

embedding-use-is-retrieval-only :
  ∀ {𝕂} (e : RetrievalEmbedding 𝕂) → embeddingRole e ≡ retrievalHint
embedding-use-is-retrieval-only = embedding-role-is-retrieval-only
