module DASHI.Mathematics.Symmetry.DiamondFccPrimitiveGlideExact where

-- Diamond two-sublattice geometry in conventional cubic quarter-cell
-- integer coordinates. It extends the existing crystal/Weyl programme
-- without replacing the original #1249 ternary 27/26/13 carrier.
--
-- External attribution: IUCr, International Tables Vol A, Fd-3m No.227;
-- AFLOW A_cF8_227_a-001 diamond conventional fcc structure.
-- In conventional-cell units fcc primitive basis is
-- (0,1/2,1/2), (1/2,0,1/2), (1/2,1/2,0).
-- Here all coordinates are multiplied by 4 (to avoid rational division).
--
-- One explicit affine glide on actual diamond sites:
--   G_x(r)=(1,1,1)+diag(-1,1,1)*r  [quarter-cell units]
-- and G_x²(r)=r+(0,2,2), a primitive fcc translation.
-- This is an exact coordinate identity, not an optical/spin experiment.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; _+_; _*_; -_)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import Data.Integer.Properties as IntP
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR
import DASHI.Mathematics.Symmetry.TetragonalIntegralLatticeActionExact as L

module RingZ = NR IntRS.ring
open RingZ using (Κ; Ι; _⊕_; _⊗_; ⊝_; solve)

record PrimitiveFcc : Set where
  constructor primitive
  field
    u v w : ℤ
open PrimitiveFcc public

-- The primitive translational lattice is infinite and integral.
fccPoint : PrimitiveFcc → L.Triple ℤ
fccPoint (primitive p q r) =
  L.xyz ((+ 2) * (q + r))
        ((+ 2) * (p + r))
        ((+ 2) * (p + q))

quarterDelta : L.Triple ℤ → L.Triple ℤ
quarterDelta (L.xyz x y z) =
  L.xyz ((+ 1) + x) ((+ 1) + y) ((+ 1) + z)

shiftPrimitive1 : PrimitiveFcc → PrimitiveFcc
shiftPrimitive1 (primitive p q r) = primitive (p + (+ 1)) q r

shiftFcc1 : L.Triple ℤ → L.Triple ℤ
shiftFcc1 (L.xyz x y z) =
  L.xyz x (y + (+ 2)) (z + (+ 2))

swapXY : PrimitiveFcc → PrimitiveFcc
swapXY (primitive p q r) = primitive q p r

swapYZ : PrimitiveFcc → PrimitiveFcc
swapYZ (primitive p q r) = primitive p r q

flipXPrimitive : PrimitiveFcc → PrimitiveFcc
flipXPrimitive (primitive p q r) =
  primitive ((p + q) + r) (- r) (- q)

flipXPoint : L.Triple ℤ → L.Triple ℤ
flipXPoint (L.xyz x y z) = L.xyz (- x) y z

swapXYPoint : L.Triple ℤ → L.Triple ℤ
swapXYPoint (L.xyz x y z) = L.xyz y x z

swapYZPoint : L.Triple ℤ → L.Triple ℤ
swapYZPoint (L.xyz x y z) = L.xyz x z y

glideXPoint : L.Triple ℤ → L.Triple ℤ
glideXPoint x = quarterDelta (flipXPoint x)

tripleExt : ∀ {p q : L.Triple ℤ} →
  L.x p ≡ L.x q → L.y p ≡ L.y q → L.z p ≡ L.z q → p ≡ q
tripleExt {L.xyz x y z} {L.xyz .x .y .z} refl refl refl = refl

primitiveExt : ∀ {p q : PrimitiveFcc} →
  u p ≡ u q → v p ≡ v q → w p ≡ w q → p ≡ q
primitiveExt {primitive p q r} {primitive .p .q .r} refl refl refl = refl

fccSwapXY : (p : PrimitiveFcc) →
  fccPoint (swapXY p) ≡ swapXYPoint (fccPoint p)
fccSwapXY (primitive p q r) =
  tripleExt refl refl
    (cong ((+ 2) *_) (IntP.+-comm q p))

fccSwapYZ : (p : PrimitiveFcc) →
  fccPoint (swapYZ p) ≡ swapYZPoint (fccPoint p)
fccSwapYZ (primitive p q r) =
  tripleExt
    (RingZ.solve 3
      (λ p q r → ((Κ (+ 2) ⊗ (r ⊕ q)) ,
                  (Κ (+ 2) ⊗ (q ⊕ r))))
      refl p q r)
    refl refl

fccFlipX : (p : PrimitiveFcc) →
  fccPoint (flipXPrimitive p) ≡ flipXPoint (fccPoint p)
fccFlipX (primitive p q r) =
  tripleExt
    (RingZ.solve 3
      (λ p q r →
        (Κ (+ 2) ⊗ (⊝ r ⊕ ⊝ q) ,
         ⊝ (Κ (+ 2) ⊗ (q ⊕ r))))
      refl p q r)
    (RingZ.solve 3
      (λ p q r →
        (Κ (+ 2) ⊗ (((p ⊕ q) ⊕ r) ⊕ ⊝ q) ,
         Κ (+ 2) ⊗ (p ⊕ r)))
      refl p q r)
    (RingZ.solve 3
      (λ p q r →
        (Κ (+ 2) ⊗ (((p ⊕ q) ⊕ r) ⊕ ⊝ r) ,
         Κ (+ 2) ⊗ (p ⊕ q)))
      refl p q r)

fccShiftPrimitive1 : (p : PrimitiveFcc) →
  fccPoint (shiftPrimitive1 p) ≡ shiftFcc1 (fccPoint p)
fccShiftPrimitive1 (primitive p q r) =
  tripleExt refl
    (RingZ.solve 3
      (λ p q r →
        (Κ (+ 2) ⊗ ((p ⊕ Κ (+ 1)) ⊕ r) ,
         (Κ (+ 2) ⊗ (p ⊕ r)) ⊕ Κ (+ 2)))
      refl p q r)
    (RingZ.solve 3
      (λ p q r →
        (Κ (+ 2) ⊗ ((p ⊕ Κ (+ 1)) ⊕ q) ,
         (Κ (+ 2) ⊗ (p ⊕ q)) ⊕ Κ (+ 2)))
      refl p q r)

-- A genuine two-atom motif; the B sublattice is shifted by (1,1,1)
-- in quarter-cell units. Both sites can have the same atomic species
-- or distinct defect labels; the latter breaks many symmetries.
data DiamondSite : Set where
  A B : PrimitiveFcc → DiamondSite

sitePosition : DiamondSite → L.Triple ℤ
sitePosition (A p) = fccPoint p
sitePosition (B p) = quarterDelta (fccPoint p)

swapXYSite : DiamondSite → DiamondSite
swapXYSite (A p) = A (swapXY p)
swapXYSite (B p) = B (swapXY p)

swapYZSite : DiamondSite → DiamondSite
swapYZSite (A p) = A (swapYZ p)
swapYZSite (B p) = B (swapYZ p)

glideXSite : DiamondSite → DiamondSite
glideXSite (A p) = B (flipXPrimitive p)
glideXSite (B p) = A (shiftPrimitive1 (flipXPrimitive p))

translation1 : DiamondSite → DiamondSite
translation1 (A p) = A (shiftPrimitive1 p)
translation1 (B p) = B (shiftPrimitive1 p)

-- The nontrivial nonsymmorphic relation is now on the actual
-- infinite two-sublattice site carrier (not only on labels).
flipPrimitiveTwice : (p : PrimitiveFcc) →
  flipXPrimitive (flipXPrimitive p) ≡ p
flipPrimitiveTwice (primitive p q r) =
  primitiveExt
    (RingZ.solve 3
      (λ p q r →
        ((((p ⊕ q) ⊕ r) ⊕ ⊝ r) ⊕ ⊝ q , p))
      refl p q r)
    (RingZ.solve 3 (λ p q r → (⊝ (⊝ q) , q)) refl p q r)
    (RingZ.solve 3 (λ p q r → (⊝ (⊝ r) , r)) refl p q r)

flipPrimitiveShift1 : (p : PrimitiveFcc) →
  flipXPrimitive (shiftPrimitive1 p) ≡
  shiftPrimitive1 (flipXPrimitive p)
flipPrimitiveShift1 (primitive p q r) =
  primitiveExt
    (RingZ.solve 3
      (λ p q r →
        ( (((p ⊕ Κ (+ 1)) ⊕ q) ⊕ r)
        , (((p ⊕ q) ⊕ r) ⊕ Κ (+ 1)) ))
      refl p q r)
    refl refl

glideSquareIsFccTranslation :
  (site : DiamondSite) →
  glideXSite (glideXSite site) ≡ translation1 site
glideSquareIsFccTranslation (A p) =
  cong (λ t → A (shiftPrimitive1 t)) (flipPrimitiveTwice p)
glideSquareIsFccTranslation (B p) =
  cong B (trans (flipPrimitiveShift1 (flipXPrimitive p))
                (cong shiftPrimitive1 (flipPrimitiveTwice p)))

swapXYSitePosition :
  (s : DiamondSite) →
  sitePosition (swapXYSite s) ≡ swapXYPoint (sitePosition s)
swapXYSitePosition (A p) = fccSwapXY p
swapXYSitePosition (B p) = cong quarterDelta (fccSwapXY p)

-- On a chosen diamond N-vacancy bond, only those permutations
-- that fix BOTH site locations survive. This is not the same as
-- a C3 permutation of spin-one energy levels.

swapYZSitePosition :
  (s : DiamondSite) →
  sitePosition (swapYZSite s) ≡ swapYZPoint (sitePosition s)
swapYZSitePosition (A p) = fccSwapYZ p
swapYZSitePosition (B p) = cong quarterDelta (fccSwapYZ p)

glideDeltaCompatibility : (p : L.Triple ℤ) →
  shiftFcc1 (flipXPoint p) ≡ glideXPoint (quarterDelta p)
glideDeltaCompatibility (L.xyz x y z) =
  tripleExt
    (RingZ.solve 1
      (λ x → (⊝ x , Κ (+ 1) ⊕ ⊝ (Κ (+ 1) ⊕ x)))
      refl x)
    (RingZ.solve 1
      (λ y → (y ⊕ Κ (+ 2) , Κ (+ 1) ⊕ (Κ (+ 1) ⊕ y)))
      refl y)
    (RingZ.solve 1
      (λ z → (z ⊕ Κ (+ 2) , Κ (+ 1) ⊕ (Κ (+ 1) ⊕ z)))
      refl z)

glideXSitePosition : (s : DiamondSite) →
  sitePosition (glideXSite s) ≡ glideXPoint (sitePosition s)
glideXSitePosition (A p) =
  cong quarterDelta (fccFlipX p)
glideXSitePosition (B p) =
  trans (fccShiftPrimitive1 (flipXPrimitive p))
    (trans
      (cong shiftFcc1 (fccFlipX p))
      (glideDeltaCompatibility (fccPoint p)))

quarterDeltaCommutesShiftFcc1 : (p : L.Triple ℤ) →
  quarterDelta (shiftFcc1 p) ≡ shiftFcc1 (quarterDelta p)
quarterDeltaCommutesShiftFcc1 (L.xyz x y z) =
  tripleExt refl
    (RingZ.solve 1
      (λ y → (Κ (+ 1) ⊕ (y ⊕ Κ (+ 2)) ,
                (Κ (+ 1) ⊕ y) ⊕ Κ (+ 2)))
      refl y)
    (RingZ.solve 1
      (λ z → (Κ (+ 1) ⊕ (z ⊕ Κ (+ 2)) ,
                (Κ (+ 1) ⊕ z) ⊕ Κ (+ 2)))
      refl z)

translation1Position :
  (s : DiamondSite) →
  sitePosition (translation1 s) ≡ shiftFcc1 (sitePosition s)
translation1Position (A p) = fccShiftPrimitive1 p
translation1Position (B p) =
  trans (cong quarterDelta (fccShiftPrimitive1 p))
        (quarterDeltaCommutesShiftFcc1 (fccPoint p))
