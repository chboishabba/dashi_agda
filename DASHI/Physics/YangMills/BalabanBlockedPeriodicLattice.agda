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
splitFinePoint {M = M} {L = L} (cube4 f₀ f₁ f₂ f₃) =
  blockedCube4
    (cube4
      (proj₁ (remQuot {m = M} L f₀))
      (proj₁ (remQuot {m = M} L f₁))
      (proj₁ (remQuot {m = M} L f₂))
      (proj₁ (remQuot {m = M} L f₃)))
    (cube4
      (proj₂ (remQuot {m = M} L f₀))
      (proj₂ (remQuot {m = M} L f₁))
      (proj₂ (remQuot {m = M} L f₂))
      (proj₂ (remQuot {m = M} L f₃)))

splitFinePointFinePoint :
  ∀ {M L : Nat}
  (blocked : BlockedCube4 M L) →
  splitFinePoint (finePoint blocked) ≡ blocked
splitFinePointFinePoint {M = M} {L = L}
  (blockedCube4
    (cube4 c₀ c₁ c₂ c₃)
    (cube4 o₀ o₁ o₂ o₃)) =
  cong₂ blockedCube4
    (cube4Ext
      (cong proj₁ (remQuot-combine {n = M} {k = L} c₀ o₀))
      (cong proj₁ (remQuot-combine {n = M} {k = L} c₁ o₁))
      (cong proj₁ (remQuot-combine {n = M} {k = L} c₂ o₂))
      (cong proj₁ (remQuot-combine {n = M} {k = L} c₃ o₃)))
    (cube4Ext
      (cong proj₂ (remQuot-combine {n = M} {k = L} c₀ o₀))
      (cong proj₂ (remQuot-combine {n = M} {k = L} c₁ o₁))
      (cong proj₂ (remQuot-combine {n = M} {k = L} c₂ o₂))
      (cong proj₂ (remQuot-combine {n = M} {k = L} c₃ o₃)))

finePointSplitFinePoint :
  ∀ {M L : Nat}
  (fine : Cube4 (M * L)) →
  finePoint (splitFinePoint fine) ≡ fine
finePointSplitFinePoint {M = M} {L = L} (cube4 f₀ f₁ f₂ f₃) =
  cube4Ext
    (combine-remQuot {n = M} L f₀)
    (combine-remQuot {n = M} L f₁)
    (combine-remQuot {n = M} L f₂)
    (combine-remQuot {n = M} L f₃)

coarseOfFine :
  ∀ {M L : Nat} →
  Cube4 (M * L) →
  Cube4 M
coarseOfFine {M = M} {L = L} fine =
  coarseCube (splitFinePoint {M = M} {L = L} fine)

offsetOfFine :
  ∀ {M L : Nat} →
  Cube4 (M * L) →
  Cube4 L
offsetOfFine {M = M} {L = L} fine =
  blockOffset (splitFinePoint {M = M} {L = L} fine)

finePointFromCoarseAndOffset :
  ∀ {M L : Nat}
  (fine : Cube4 (M * L)) →
  finePoint
    (blockedCube4
      (coarseOfFine {M = M} {L = L} fine)
      (offsetOfFine {M = M} {L = L} fine))
  ≡ fine
finePointFromCoarseAndOffset {M = M} {L = L} fine =
  finePointSplitFinePoint {M = M} {L = L} fine
