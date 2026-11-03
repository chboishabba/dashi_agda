{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayNativeCyclicFinIsoSafeExact where

------------------------------------------------------------------------
-- R445 finite geometry: original periodic CyclicIndex N = Fin N.
--
-- Pure finite carrier identification, with explicit two-sided inverses.
-- Reuses the original CyclicIndex constructors and stdlib Fin constructors.
-- This is a structural coordinate theorem, not a measure/RG estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Fin.Base as Fin
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus

cyclicToFin :
  ∀ {N} → Torus.CyclicIndex N → Fin.Fin N
cyclicToFin Torus.zeroᵢ = Fin.zero
cyclicToFin (Torus.sucᵢ index) = Fin.suc (cyclicToFin index)

finToCyclic :
  ∀ {N} → Fin.Fin N → Torus.CyclicIndex N
finToCyclic Fin.zero = Torus.zeroᵢ
finToCyclic (Fin.suc index) = Torus.sucᵢ (finToCyclic index)

cyclicRoundtrip :
  ∀ {N} (index : Torus.CyclicIndex N) →
  finToCyclic (cyclicToFin index) ≡ index
cyclicRoundtrip Torus.zeroᵢ = refl
cyclicRoundtrip (Torus.sucᵢ index) =
  cong Torus.sucᵢ (cyclicRoundtrip index)

finRoundtrip :
  ∀ {N} (index : Fin.Fin N) →
  cyclicToFin (finToCyclic index) ≡ index
finRoundtrip Fin.zero = refl
finRoundtrip (Fin.suc index) =
  cong Fin.suc (finRoundtrip index)
