module DASHI.Algebra.PhysicsConformance where

open import Agda.Builtin.List     using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Unit             using (⊤; tt)
open import Data.Product          using (_×_; _,_)

open import DASHI.Algebra.PhysicsSignature using (Sig15)
open import DASHI.Algebra.PhysicsTable using (State; vectors; implSig; specSig)

-- Conformance on a finite list:
ConformsOn : (f g : State → Sig15) → List State → Set
ConformsOn f g []       = ⊤
ConformsOn f g (s ∷ ss) = (f s ≡ g s) × ConformsOn f g ss

-- This is the closure theorem you “ship”:
-- now fully concrete via the PhysicsTable witnesses.
physics-conformance : ConformsOn implSig specSig vectors
physics-conformance = go vectors
  where
    go : (vs : List State) → ConformsOn implSig specSig vs
    go []       = tt
    go (s ∷ ss) = refl , go ss
