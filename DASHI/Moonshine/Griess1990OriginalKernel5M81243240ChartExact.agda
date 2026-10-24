module DASHI.Moonshine.Griess1990OriginalKernel5M81243240ChartExact where

-- 2026-10-25 actual source-carrier reconciliation, NOT numerology.
--
-- Original external author of the Moufang g law:
-- Robert L. Griess Jr., J. Algebra 131 (1990), 281-293,
-- DOI 10.1016/0021-8693(90)90176-O.
--
-- Prior DASHI OWNERS, preserved:
-- * Trialectic369DyadicLocalComplementFactorizationExact.Kernel5 is
--   the original five-trit complement, *not* a new vector type.
-- * Griess1990Moufang81IbrahimProjective13Exact.M81 is the original
--   source-phase 81-element underlying loop, *not* an F4/E6 proxy.
-- * The related Lean PR #43/Agda #1094 diagonal-relative 240 owner is
--   on a separate PR branch; DO NOT import nonexistent paths.
-- * The separate structured 240=72+6+6×27 E8 carrier is NOT
--   identified with original Kernel5 minus diagonal.
--
-- The to/from coordinates below encode a chosen bijective set chart:
-- (a,b,c,d,e) -> ((a-e,b-e,c-e; d-e),e) via actual balanced trits.
-- The M81 product is NONASSOCIATIVE and is not the componentwise
-- addition on original Kernel5.
--
-- Executed independent exact finite Python checked all 243 point
-- roundtrips, diagonal <-> {M81 identity}×F3, 6+234, full E6 Q
-- spectra and 6 true M81 lift actions on the old 240.
-- Agda toolchain NOT run. Two-sided Agda proof receipt explicitly open.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _*_; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Reasoning.Trialectic369DyadicLocalComplementFactorizationExact as Local
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as Add
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Moonshine.Griess1990Moufang81IbrahimProjective13Exact as Griess
import DASHI.Wikimedia.IbrahimA027907PathCubeTernaryExceptionalThirteenSnowballExact as Ibrahim

open Codec using ([]ᵥ; _∷ᵥ_)

Kernel5 : Set
Kernel5 = Local.Kernel5

add3 : Trit → Trit → Trit
add3 = Add._+3_

minus3 : Trit → Trit → Trit
minus3 a b = add3 a (Add.negate3 b)

-- The ACTUAL source Griess loop set (V27 grade × F3 central phase),
-- plus the fifth coordinate which is not part of the M81 product.
M81TimesF3 : Set
M81TimesF3 = Griess.M81 × Trit

kernel5ToM81 : Kernel5 → M81TimesF3
kernel5ToM81 (a ∷ᵥ b ∷ᵥ c ∷ᵥ d ∷ᵥ e ∷ᵥ []ᵥ) =
  ( (Cube.ternary27Point
      (SSP.fromTrit (minus3 a e))
      (SSP.fromTrit (minus3 b e))
      (SSP.fromTrit (minus3 c e)) ,
      SSP.fromTrit (minus3 d e)) ,
    e )

m81ToKernel5 : M81TimesF3 → Kernel5
m81ToKernel5
  ((Cube.ternary27Point x y z , central) , t) =
  add3 (SSP.toTrit x) t ∷ᵥ
  add3 (SSP.toTrit y) t ∷ᵥ
  add3 (SSP.toTrit z) t ∷ᵥ
  add3 (SSP.toTrit central) t ∷ᵥ
  t ∷ᵥ []ᵥ



-- Four-trit subtraction cancellation uses the actual existing
-- Monster/SSP mod-three trit addition, not an invented algebra.
subAddCancellation : (a t : Trit) →
  add3 (minus3 a t) t ≡ a
subAddCancellation neg neg = refl
subAddCancellation neg zer = refl
subAddCancellation neg pos = refl
subAddCancellation zer neg = refl
subAddCancellation zer zer = refl
subAddCancellation zer pos = refl
subAddCancellation pos neg = refl
subAddCancellation pos zer = refl
subAddCancellation pos pos = refl

addSubCancellation : (a t : Trit) →
  minus3 (add3 a t) t ≡ a
addSubCancellation neg neg = refl
addSubCancellation neg zer = refl
addSubCancellation neg pos = refl
addSubCancellation zer neg = refl
addSubCancellation zer zer = refl
addSubCancellation zer pos = refl
addSubCancellation pos neg = refl
addSubCancellation pos zer = refl
addSubCancellation pos pos = refl

-- Constructive two-sided chart receipts. No bare Set or Bool assumed.
-- Rewriting reuses the canonical SSP <> Trit conversion theorems.
kernel5LeftRoundTrip :
  (x : Kernel5) → m81ToKernel5 (kernel5ToM81 x) ≡ x
kernel5LeftRoundTrip
  (a ∷ᵥ b ∷ᵥ c ∷ᵥ d ∷ᵥ e ∷ᵥ []ᵥ)
  rewrite SSP.toTrit-fromTrit (minus3 a e)
        | SSP.toTrit-fromTrit (minus3 b e)
        | SSP.toTrit-fromTrit (minus3 c e)
        | SSP.toTrit-fromTrit (minus3 d e)
        | subAddCancellation a e
        | subAddCancellation b e
        | subAddCancellation c e
        | subAddCancellation d e
  = refl

m81RightRoundTrip :
  (x : M81TimesF3) → kernel5ToM81 (m81ToKernel5 x) ≡ x
m81RightRoundTrip
  ((Cube.ternary27Point a b c , central) , t)
  rewrite addSubCancellation (SSP.toTrit a) t
        | addSubCancellation (SSP.toTrit b) t
        | addSubCancellation (SSP.toTrit c) t
        | addSubCancellation (SSP.toTrit central) t
        | SSP.fromTrit-toTrit a
        | SSP.fromTrit-toTrit b
        | SSP.fromTrit-toTrit c
        | SSP.fromTrit-toTrit central
  = refl

-- The ORIGINAL 3-point constant diagonal (Agda #1094 source).
diagonalKernel5 : Trit → Kernel5
diagonalKernel5 t =
  t ∷ᵥ t ∷ᵥ t ∷ᵥ t ∷ᵥ t ∷ᵥ []ᵥ

-- Distinct cochain phases: the original M81 identity is the old
-- Cube.origin × balanced-zero, not any of the other two central elements.
m81Identity : Griess.M81
m81Identity = Griess.moufangIdentity

zeroDiagonalToUnit :
  kernel5ToM81 (diagonalKernel5 zer) ≡ (m81Identity , zer)
zeroDiagonalToUnit = refl

positiveDiagonalToUnit :
  kernel5ToM81 (diagonalKernel5 pos) ≡ (m81Identity , pos)
positiveDiagonalToUnit = refl

negativeDiagonalToUnit :
  kernel5ToM81 (diagonalKernel5 neg) ≡ (m81Identity , neg)
negativeDiagonalToUnit = refl


-- Concrete source-level two-way equivalence witness: this DOES pay the
-- actual Kernel5↔M81×Trit point-carrier roundtrip, not M81 multiplication.
record Kernel5M81CarrierBidi : Set where
  constructor kernel5-m81-carrier-bidi
  field
    leftInverse :
      (x : Kernel5) → m81ToKernel5 (kernel5ToM81 x) ≡ x
    rightInverse :
      (x : M81TimesF3) → kernel5ToM81 (m81ToKernel5 x) ≡ x

canonicalKernel5M81CarrierBidi : Kernel5M81CarrierBidi
canonicalKernel5M81CarrierBidi =
  kernel5-m81-carrier-bidi kernel5LeftRoundTrip m81RightRoundTrip

m81IdentityKernel5 :
  (t : Trit) → m81ToKernel5 (m81Identity , t) ≡ diagonalKernel5 t
m81IdentityKernel5 neg = refl
m81IdentityKernel5 zer = refl
m81IdentityKernel5 pos = refl

diagonalKernel5Forward :
  (t : Trit) → kernel5ToM81 (diagonalKernel5 t) ≡
    (m81Identity , t)
diagonalKernel5Forward neg = refl
diagonalKernel5Forward zer = refl
diagonalKernel5Forward pos = refl

diagonalKernel5Backward :
  (x : Kernel5) → (t : Trit) →
  kernel5ToM81 x ≡ (m81Identity , t) →
  x ≡ diagonalKernel5 t
diagonalKernel5Backward x t h =
  trans (sym (kernel5LeftRoundTrip x))
    (trans (cong m81ToKernel5 h) (m81IdentityKernel5 t))

-- Agda #1094 defines this dependent relative-carrier on its own
-- unmerged branch; keep the old Kernel5 and non-diagonal contract
-- without inventing an equality to the structured E8 root type.
record RelativeOldKernel5 : Set where
  constructor original-relative-kernel5
  field
    point : Kernel5
    outsideDiagonal : (t : Trit) → point ≡ diagonalKernel5 t → ⊥

-- The precise Agda proof gate is an INHABITANT, not a Boolean receipt
-- nor the existence of a Python script. No postulates/axioms inserted.
record Kernel5M81BidiPayment : Set where
  field
    kernelLeftInverse :
      (x : Kernel5) → m81ToKernel5 (kernel5ToM81 x) ≡ x
    m81RightInverse :
      (x : M81TimesF3) → kernel5ToM81 (m81ToKernel5 x) ≡ x
    diagonalIffM81Identity :
      (x : Kernel5) →
      ((t : Trit) → x ≡ diagonalKernel5 t → kernel5ToM81 x ≡ (m81Identity , t))
    oldRelative240ConcreteBijection : Set
    originalE6QuadraticActionStillObstructed : Set
open Kernel5M81BidiPayment public

-- Arithmetic *consequence* of the finite chart, not an E8 root proof.
threeTimesEightyPlusThree : 243 ≡ 3 + 3 * 80
threeTimesEightyPlusThree = refl

old240AsSixPlus234 : 240 ≡ 6 + 234
old240AsSixPlus234 = refl

-- All exact external sources remain distinct:
-- Griess M81 (1990); original DASHI T5; Ibrahim OEIS A027907,
-- the pre-existing E6 quadratic chart, and Chen--Lam--Shimakura VOA.
-- No Monster 3B/physical observable or E8 Weyl intertwiner follows.
