module DASHI.Physics.YangMills.BalabanBlockedPeriodicLattice where

------------------------------------------------------------------------
-- Exact finite block decomposition of the periodic four-dimensional lattice.
--
-- At side M * L, every fine coordinate is uniquely a pair
--
--   (coarse coordinate in Fin M, offset in Fin L).
--
-- `Data.Fin.combine` and `remQuot` implement this bijection.  Applying it in
-- each of the four coordinate directions gives a literal decomposition
--
--   Cube4 (M * L)  ≃  Cube4 M × Cube4 L.
--
-- This is the missing finite carrier relation behind Bałaban's blocks B(y).
-- It introduces no averaging or analytic theorem: both round-trip laws are
-- proved from the finite-index arithmetic.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Fin.Base using
  ( combine
  ; remQuot
  )
open import Data.Fin.Properties using
  ( remQuot-combine
  ; combine-remQuot
  )
open import Data.Product.Base using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using
  ( Cube4
  ; cube4
  ; cube4Ext
  )

record BlockedCube4 (M L : Nat) : Set where
  constructor blockedCube4
  field
    coarseCube : Cube4 M
    blockOffset : Cube4 L

open BlockedCube4 public

finePoint :
  ∀ {M L : Nat} →
  BlockedCube4 M L →
  Cube4 (M * L)
finePoint
  (blockedCube4
    (cube4 c₀ c₁ c₂ c₃)
    (cube4 o₀ o₁ o₂ o₃)) =
  cube4
    (combine c₀ o₀)
    (combine c₁ o₁)
    (combine c₂ o₂)
    (combine c₃ o₃)

splitFinePoint :
  ∀ {M L : Nat} →
  Cube4 (M * L) →
  BlockedCube4 M L
splitFinePoint {L = L} (cube4 f₀ f₁ f₂ f₃) =
  blockedCube4
    (cube4
      (proj₁ (remQuot L f₀))
      (proj₁ (remQuot L f₁))
      (proj₁ (remQuot L f₂))
      (proj₁ (remQuot L f₃)))
    (cube4
      (proj₂ (remQuot L f₀))
      (proj₂ (remQuot L f₁))
      (proj₂ (remQuot L f₂))
      (proj₂ (remQuot L f₃)))

splitFinePointFinePoint :
  ∀ {M L : Nat}
  (blocked : BlockedCube4 M L) →
  splitFinePoint (finePoint blocked) ≡ blocked
splitFinePointFinePoint {L = L}
  (blockedCube4
    (cube4 c₀ c₁ c₂ c₃)
    (cube4 o₀ o₁ o₂ o₃)) =
  cong₂ blockedCube4
    (cube4Ext
      (cong proj₁ (remQuot-combine c₀ o₀))
      (cong proj₁ (remQuot-combine c₁ o₁))
      (cong proj₁ (remQuot-combine c₂ o₂))
      (cong proj₁ (remQuot-combine c₃ o₃)))
    (cube4Ext
      (cong proj₂ (remQuot-combine c₀ o₀))
      (cong proj₂ (remQuot-combine c₁ o₁))
      (cong proj₂ (remQuot-combine c₂ o₂))
      (cong proj₂ (remQuot-combine c₃ o₃)))

finePointSplitFinePoint :
  ∀ {M L : Nat}
  (fine : Cube4 (M * L)) →
  finePoint (splitFinePoint fine) ≡ fine
finePointSplitFinePoint {L = L} (cube4 f₀ f₁ f₂ f₃) =
  cube4Ext
    (combine-remQuot L f₀)
    (combine-remQuot L f₁)
    (combine-remQuot L f₂)
    (combine-remQuot L f₃)

coarseOfFine :
  ∀ {M L : Nat} →
  Cube4 (M * L) →
  Cube4 M
coarseOfFine fine = coarseCube (splitFinePoint fine)

offsetOfFine :
  ∀ {M L : Nat} →
  Cube4 (M * L) →
  Cube4 L
offsetOfFine fine = blockOffset (splitFinePoint fine)

finePointFromCoarseAndOffset :
  ∀ {M L : Nat}
  (fine : Cube4 (M * L)) →
  finePoint
    (blockedCube4
      (coarseOfFine fine)
      (offsetOfFine fine))
  ≡ fine
finePointFromCoarseAndOffset = finePointSplitFinePoint
