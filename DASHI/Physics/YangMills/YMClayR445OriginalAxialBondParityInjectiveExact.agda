module DASHI.Physics.YangMills.YMClayR445OriginalAxialBondParityInjectiveExact where

------------------------------------------------------------------------
-- P0.A exact 4D periodic coordinate PARITY certificate.
-- An original side-two coarse oriented bond (X,mu), together with
-- a two-step phase 0 or 1, encodes into a side-four positive bond
-- (2X+phase*e_mu,mu). Its explicitly defined partial decoder is a
-- LEFT INVERSE, therefore all 64 x 2 selected positive bonds are
-- distinct, including both axial phases and periodic wrap.
--
-- Pure FINITE cyclic-index geometry. No physical Wilson measure,
-- real-field postulates, Fubini, continuum assumption or RG estimate.
-- The separate P0.C comparison with the ACTUAL native Balaban
-- fineBlockOrigin remains a mandatory original-source weld.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as T

Bit : Set
Bit = T.CyclicIndex 2

Quad : Set
Quad = T.CyclicIndex 4

Site2 : Set
Site2 = T.periodicTorus4Definition 2

Site4 : Set
Site4 = T.periodicTorus4Definition 4

CoarseBond : Set
CoarseBond = T.PositiveBond 2

FineBond : Set
FineBond = T.PositiveBond 4

Axis : Set
Axis = T.Axis4

-- Exact 0,1,2,3 ordering within the ORIGINAL CyclicIndex carriers.
coord : Bit → Bit → Quad
coord T.zeroᵢ T.zeroᵢ = T.zeroᵢ
coord T.zeroᵢ (T.sucᵢ T.zeroᵢ) = T.sucᵢ T.zeroᵢ
coord (T.sucᵢ T.zeroᵢ) T.zeroᵢ =
  T.sucᵢ (T.sucᵢ T.zeroᵢ)
coord (T.sucᵢ T.zeroᵢ) (T.sucᵢ T.zeroᵢ) =
  T.sucᵢ (T.sucᵢ (T.sucᵢ T.zeroᵢ))

coarse : Quad → Bit
coarse T.zeroᵢ = T.zeroᵢ
coarse (T.sucᵢ T.zeroᵢ) = T.zeroᵢ
coarse (T.sucᵢ (T.sucᵢ T.zeroᵢ)) = T.sucᵢ T.zeroᵢ
coarse (T.sucᵢ (T.sucᵢ (T.sucᵢ T.zeroᵢ))) =
  T.sucᵢ T.zeroᵢ

phase : Quad → Bit
phase T.zeroᵢ = T.zeroᵢ
phase (T.sucᵢ T.zeroᵢ) = T.sucᵢ T.zeroᵢ
phase (T.sucᵢ (T.sucᵢ T.zeroᵢ)) = T.zeroᵢ
phase (T.sucᵢ (T.sucᵢ (T.sucᵢ T.zeroᵢ))) =
  T.sucᵢ T.zeroᵢ

even : Bit → Quad
even b = coord b T.zeroᵢ

decodeEven : Quad → Maybe Bit
decodeEven T.zeroᵢ = just T.zeroᵢ
decodeEven (T.sucᵢ T.zeroᵢ) = nothing
decodeEven (T.sucᵢ (T.sucᵢ T.zeroᵢ)) =
  just (T.sucᵢ T.zeroᵢ)
decodeEven (T.sucᵢ (T.sucᵢ (T.sucᵢ T.zeroᵢ))) = nothing

coarseCoordRoundTrip : (b p : Bit) → coarse (coord b p) ≡ b
coarseCoordRoundTrip T.zeroᵢ T.zeroᵢ = refl
coarseCoordRoundTrip T.zeroᵢ (T.sucᵢ T.zeroᵢ) = refl
coarseCoordRoundTrip (T.sucᵢ T.zeroᵢ) T.zeroᵢ = refl
coarseCoordRoundTrip (T.sucᵢ T.zeroᵢ) (T.sucᵢ T.zeroᵢ) = refl

phaseCoordRoundTrip : (b p : Bit) → phase (coord b p) ≡ p
phaseCoordRoundTrip T.zeroᵢ T.zeroᵢ = refl
phaseCoordRoundTrip T.zeroᵢ (T.sucᵢ T.zeroᵢ) = refl
phaseCoordRoundTrip (T.sucᵢ T.zeroᵢ) T.zeroᵢ = refl
phaseCoordRoundTrip (T.sucᵢ T.zeroᵢ) (T.sucᵢ T.zeroᵢ) = refl

evenDecodeRoundTrip : (b : Bit) → decodeEven (even b) ≡ just b
evenDecodeRoundTrip T.zeroᵢ = refl
evenDecodeRoundTrip (T.sucᵢ T.zeroᵢ) = refl

-- Each original axial coarse bond owns two fine bonds, both with
-- the SAME positive orientation. All transverse fine coordinates
-- are even; the axial coordinate has the selected 0/1 phase.
originalR445SelectedFineBond : CoarseBond → Bit → FineBond
originalR445SelectedFineBond
  (T.pair (T.pair (T.pair a b) (T.pair c d)) T.zeroᵢ) p =
  T.pair
    (T.pair (T.pair (coord a p) (even b))
      (T.pair (even c) (even d)))
    T.zeroᵢ
originalR445SelectedFineBond
  (T.pair (T.pair (T.pair a b) (T.pair c d))
    (T.sucᵢ T.zeroᵢ)) p =
  T.pair
    (T.pair (T.pair (even a) (coord b p))
      (T.pair (even c) (even d)))
    (T.sucᵢ T.zeroᵢ)
originalR445SelectedFineBond
  (T.pair (T.pair (T.pair a b) (T.pair c d))
    (T.sucᵢ (T.sucᵢ T.zeroᵢ))) p =
  T.pair
    (T.pair (T.pair (even a) (even b))
      (T.pair (coord c p) (even d)))
    (T.sucᵢ (T.sucᵢ T.zeroᵢ))
originalR445SelectedFineBond
  (T.pair (T.pair (T.pair a b) (T.pair c d))
    (T.sucᵢ (T.sucᵢ (T.sucᵢ T.zeroᵢ)))) p =
  T.pair
    (T.pair (T.pair (even a) (even b))
      (T.pair (even c) (coord d p)))
    (T.sucᵢ (T.sucᵢ (T.sucᵢ T.zeroᵢ))

Selected : Set
Selected = T.Product CoarseBond Bit

-- Explicit partial decoder from ORIGINAL side-four positive bonds.
-- A fine bond belongs to the selected axial family exactly if all
-- THREE non-axial coordinates are even. Its axial parity records the
-- first/second-link phase of the unique coarse source bond.
originalR445DecodeSelectedFineBond : FineBond → Maybe Selected
originalR445DecodeSelectedFineBond
  (T.pair (T.pair (T.pair x0 x1) (T.pair x2 x3)) T.zeroᵢ)
  with decodeEven x1 | decodeEven x2 | decodeEven x3
... | just b | just c | just d =
  just (T.pair
    (T.pair
      (T.pair (T.pair (coarse x0) b) (T.pair c d))
      T.zeroᵢ)
    (phase x0))
... | _ | _ | _ = nothing
originalR445DecodeSelectedFineBond
  (T.pair (T.pair (T.pair x0 x1) (T.pair x2 x3))
    (T.sucᵢ T.zeroᵢ))
  with decodeEven x0 | decodeEven x2 | decodeEven x3
... | just a | just c | just d =
  just (T.pair
    (T.pair
      (T.pair (T.pair a (coarse x1)) (T.pair c d))
      (T.sucᵢ T.zeroᵢ))
    (phase x1))
... | _ | _ | _ = nothing
originalR445DecodeSelectedFineBond
  (T.pair (T.pair (T.pair x0 x1) (T.pair x2 x3))
    (T.sucᵢ (T.sucᵢ T.zeroᵢ)))
  with decodeEven x0 | decodeEven x1 | decodeEven x3
... | just a | just b | just d =
  just (T.pair
    (T.pair
      (T.pair (T.pair a b) (T.pair (coarse x2) d))
      (T.sucᵢ (T.sucᵢ T.zeroᵢ)))
    (phase x2))
... | _ | _ | _ = nothing
originalR445DecodeSelectedFineBond
  (T.pair (T.pair (T.pair x0 x1) (T.pair x2 x3))
    (T.sucᵢ (T.sucᵢ (T.sucᵢ T.zeroᵢ)))
  with decodeEven x0 | decodeEven x1 | decodeEven x2
... | just a | just b | just c =
  just (T.pair
    (T.pair
      (T.pair (T.pair a b) (T.pair c (coarse x3)))
      (T.sucᵢ (T.sucᵢ (T.sucᵢ T.zeroᵢ))))
    (phase x3))
... | _ | _ | _ = nothing

-- The constructive noncollision certificate: the decoder recovers
-- the EXACT original coarse bond and its axial phase, not just a
-- cardinality or an unproved inequivalence premise.
originalR445SelectedBondRoundTrip :
  (C : CoarseBond) (p : Bit) →
  originalR445DecodeSelectedFineBond
    (originalR445SelectedFineBond C p) ≡ just (T.pair C p)
originalR445SelectedBondRoundTrip
  (T.pair (T.pair (T.pair a b) (T.pair c d)) T.zeroᵢ) p
  rewrite evenDecodeRoundTrip b | evenDecodeRoundTrip c
        | evenDecodeRoundTrip d | coarseCoordRoundTrip a p
        | phaseCoordRoundTrip a p = refl
originalR445SelectedBondRoundTrip
  (T.pair (T.pair (T.pair a b) (T.pair c d))
    (T.sucᵢ T.zeroᵢ)) p
  rewrite evenDecodeRoundTrip a | evenDecodeRoundTrip c
        | evenDecodeRoundTrip d | coarseCoordRoundTrip b p
        | phaseCoordRoundTrip b p = refl
originalR445SelectedBondRoundTrip
  (T.pair (T.pair (T.pair a b) (T.pair c d))
    (T.sucᵢ (T.sucᵢ T.zeroᵢ))) p
  rewrite evenDecodeRoundTrip a | evenDecodeRoundTrip b
        | evenDecodeRoundTrip d | coarseCoordRoundTrip c p
        | phaseCoordRoundTrip c p = refl
originalR445SelectedBondRoundTrip
  (T.pair (T.pair (T.pair a b) (T.pair c d))
    (T.sucᵢ (T.sucᵢ (T.sucᵢ T.zeroᵢ)))) p
  rewrite evenDecodeRoundTrip a | evenDecodeRoundTrip b
        | evenDecodeRoundTrip c | coarseCoordRoundTrip d p
        | phaseCoordRoundTrip d p = refl

justInjective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
justInjective refl = refl

originalR445SelectedBondEncodingInjective :
  (C D : CoarseBond) (i j : Bit) →
  originalR445SelectedFineBond C i ≡
    originalR445SelectedFineBond D j →
  T.pair C i ≡ T.pair D j
originalR445SelectedBondEncodingInjective C D i j equality =
  justInjective
    (trans
      (sym (originalR445SelectedBondRoundTrip C i))
      (trans
        (cong originalR445DecodeSelectedFineBond equality)
        (originalR445SelectedBondRoundTrip D j)))

originalR445NativeCoarseBondPairIndicesInjective :
  (C D : CoarseBond) (i j : Bit) →
  originalR445SelectedFineBond C i ≡
    originalR445SelectedFineBond D j →
  C ≡ D
originalR445NativeCoarseBondPairIndicesInjective C D i j eq =
  cong T.first
    (originalR445SelectedBondEncodingInjective C D i j eq)

originalR445SelectedBondPhaseDisjoint :
  (C D : CoarseBond) (i j : Bit) →
  originalR445SelectedFineBond C i ≡
    originalR445SelectedFineBond D j →
  i ≡ j
originalR445SelectedBondPhaseDisjoint C D i j eq =
  cong T.second
    (originalR445SelectedBondEncodingInjective C D i j eq)

-- Remaining exact P0.C interface: show the EXISTING source
-- Block.fineBlockOrigin {m=1}{l=1} is the even-site map of
-- originalR445SelectedFineBond for each original coarse site.
