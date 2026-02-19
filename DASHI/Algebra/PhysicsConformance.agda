module DASHI.Algebra.PhysicsConformance where

open import Agda.Builtin.List     using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Unit             using (⊤; tt)
open import Data.Product          using (_×_; _,_)

open import DASHI.Algebra.PhysicsSignature using (State; Sig15)

-- A finite witness set (vectors) you will provide.
-- In practice: export a list of concrete States from Python/Rust
-- and import them as constructors/constants.
postulate
  vectors : List State

-- The spec signature is what the theory says (Lens-based, definitional).
postulate
  specSig : State → Sig15

-- The implementation signature is what your pipeline computes (table/extractor).
postulate
  implSig : State → Sig15

-- Conformance on a finite list:
ConformsOn : (f g : State → Sig15) → List State → Set
ConformsOn f g []       = ⊤
ConformsOn f g (s ∷ ss) = (f s ≡ g s) × ConformsOn f g ss

-- This is the closure theorem you “ship”:
-- once you fill vectors/specSig/implSig concretely, this becomes
-- a finite proof (often refls if implSig is imported as definitional table).
postulate
  physics-conformance : ConformsOn implSig specSig vectors
