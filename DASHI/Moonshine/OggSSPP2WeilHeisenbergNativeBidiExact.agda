module DASHI.Moonshine.OggSSPP2WeilHeisenbergNativeBidiExact where

------------------------------------------------------------------------
-- SAME-OBJECT COCYCLE TRANSPORT, NOT ANOTHER HEISENBERG MODEL.
--
-- Two existing owners:
--   W = OggSSPEllipticNineWeilHeisenbergFiniteActionExact
--       H3 on F3 × F3 with central exponent 1/2*(x*y'-y*x').
--   A = OggSSPP2TernaryHeisenbergAxis0Exact
--       rank-one axis-0 inside Monster3BFiniteHeisenberg H6,
--       native cocycle y*x'.
--
-- Since the two chosen alternating orientations are opposite,
--   z_Weil = -(z_native + y*x) mod 3
-- gives an exact group-law isomorphism. A centre sign flip is required;
-- omitting it would identify opposite commutator orientations.
--
-- The explicit 729 reductions below are kernel finite-field verification of
-- the existing two group laws on the same 27 input states, not a standalone
-- arithmetic assertion about the intrinsic Weil pairing on E[3].
------------------------------------------------------------------------

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Product using (_,_)

import DASHI.Moonshine.OggSSPEllipticNineWeilHeisenbergFiniteActionExact as W
import DASHI.Moonshine.OggSSPP2TernaryHeisenbergAxis0Exact as A
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H

tritToF3 : Trit → W.F3
tritToF3 neg = W.m
tritToF3 zer = W.z
tritToF3 pos = W.p

f3ToTrit : W.F3 → Trit
f3ToTrit W.m = neg
f3ToTrit W.z = zer
f3ToTrit W.p = pos

-- Reverses the centre orientation while changing unsymmetrized coordinates
-- into alternating coordinates.  Translation/modulation coordinates remain
-- in the same ordered basis.
nativeToWeil : A.RankOneHeisenberg → W.H3
nativeToWeil (A.heisenbergOne x y z) =
  W.heis
    (W.neg (W._⊕_ (tritToF3 z)
      (W._⊗_ (tritToF3 y) (tritToF3 x))))
    (tritToF3 x , tritToF3 y)

weilToNative : W.H3 → A.RankOneHeisenberg
weilToNative (W.heis z (x , y)) =
  A.heisenbergOne
    (f3ToTrit x)
    (f3ToTrit y)
    (f3ToTrit (W.neg (W._⊕_ z (W._⊗_ y x))))

nativeToWeil_roundtrip :
  (g : A.RankOneHeisenberg) → weilToNative (nativeToWeil g) ≡ g
nativeToWeil_roundtrip (A.heisenbergOne neg neg neg) = refl
nativeToWeil_roundtrip (A.heisenbergOne neg neg zer) = refl
nativeToWeil_roundtrip (A.heisenbergOne neg neg pos) = refl
nativeToWeil_roundtrip (A.heisenbergOne neg zer neg) = refl
nativeToWeil_roundtrip (A.heisenbergOne neg zer zer) = refl
nativeToWeil_roundtrip (A.heisenbergOne neg zer pos) = refl
nativeToWeil_roundtrip (A.heisenbergOne neg pos neg) = refl
nativeToWeil_roundtrip (A.heisenbergOne neg pos zer) = refl
nativeToWeil_roundtrip (A.heisenbergOne neg pos pos) = refl
nativeToWeil_roundtrip (A.heisenbergOne zer neg neg) = refl
nativeToWeil_roundtrip (A.heisenbergOne zer neg zer) = refl
nativeToWeil_roundtrip (A.heisenbergOne zer neg pos) = refl
nativeToWeil_roundtrip (A.heisenbergOne zer zer neg) = refl
nativeToWeil_roundtrip (A.heisenbergOne zer zer zer) = refl
nativeToWeil_roundtrip (A.heisenbergOne zer zer pos) = refl
nativeToWeil_roundtrip (A.heisenbergOne zer pos neg) = refl
nativeToWeil_roundtrip (A.heisenbergOne zer pos zer) = refl
nativeToWeil_roundtrip (A.heisenbergOne zer pos pos) = refl
nativeToWeil_roundtrip (A.heisenbergOne pos neg neg) = refl
nativeToWeil_roundtrip (A.heisenbergOne pos neg zer) = refl
nativeToWeil_roundtrip (A.heisenbergOne pos neg pos) = refl
nativeToWeil_roundtrip (A.heisenbergOne pos zer neg) = refl
nativeToWeil_roundtrip (A.heisenbergOne pos zer zer) = refl
nativeToWeil_roundtrip (A.heisenbergOne pos zer pos) = refl
nativeToWeil_roundtrip (A.heisenbergOne pos pos neg) = refl
nativeToWeil_roundtrip (A.heisenbergOne pos pos zer) = refl
nativeToWeil_roundtrip (A.heisenbergOne pos pos pos) = refl

weilToNative_roundtrip :
  (g : W.H3) → nativeToWeil (weilToNative g) ≡ g
weilToNative_roundtrip (W.heis m (m , m)) = refl
weilToNative_roundtrip (W.heis z (m , m)) = refl
weilToNative_roundtrip (W.heis p (m , m)) = refl
weilToNative_roundtrip (W.heis m (m , z)) = refl
weilToNative_roundtrip (W.heis z (m , z)) = refl
weilToNative_roundtrip (W.heis p (m , z)) = refl
weilToNative_roundtrip (W.heis m (m , p)) = refl
weilToNative_roundtrip (W.heis z (m , p)) = refl
weilToNative_roundtrip (W.heis p (m , p)) = refl
weilToNative_roundtrip (W.heis m (z , m)) = refl
weilToNative_roundtrip (W.heis z (z , m)) = refl
weilToNative_roundtrip (W.heis p (z , m)) = refl
weilToNative_roundtrip (W.heis m (z , z)) = refl
weilToNative_roundtrip (W.heis z (z , z)) = refl
weilToNative_roundtrip (W.heis p (z , z)) = refl
weilToNative_roundtrip (W.heis m (z , p)) = refl
weilToNative_roundtrip (W.heis z (z , p)) = refl
weilToNative_roundtrip (W.heis p (z , p)) = refl
weilToNative_roundtrip (W.heis m (p , m)) = refl
weilToNative_roundtrip (W.heis z (p , m)) = refl
weilToNative_roundtrip (W.heis p (p , m)) = refl
weilToNative_roundtrip (W.heis m (p , z)) = refl
weilToNative_roundtrip (W.heis z (p , z)) = refl
weilToNative_roundtrip (W.heis p (p , z)) = refl
weilToNative_roundtrip (W.heis m (p , p)) = refl
weilToNative_roundtrip (W.heis z (p , p)) = refl
weilToNative_roundtrip (W.heis p (p , p)) = refl

-- All 27×27 products are equations between the two ALREADY SELECTED
-- cocycles; no separate H3 product has been introduced here.
nativeToWeil_compose :
  (g h : A.RankOneHeisenberg) →
  nativeToWeil (A.composeOne g h) ≡ W.hprod (nativeToWeil g) (nativeToWeil h)
nativeToWeil_compose (A.heisenbergOne neg neg neg) (A.heisenbergOne neg neg neg) = refl
nativeToWeil_compose (A.heisenbergOne neg neg neg) (A.heisenbergOne neg neg zer) = refl
nativeToWeil_compose (A.heisenbergOne neg neg neg) (A.heisenbergOne neg neg pos) = refl
nativeToWeil_compose (A.heisenbergOne neg neg neg) (A.heisenbergOne neg zer neg) = refl
nativeToWeil_compose (A.heisenbergOne neg neg neg) (A.heisenbergOne neg zer zer) = refl
nativeToWeil_compose (A.heisenbergOne neg neg neg) (A.heisenbergOne neg zer pos) = refl
nativeToWeil_compose (A.heisenbergOne neg neg neg) (A.heisenbergOne neg pos neg) = refl
nativeToWeil_compose (A.heisenbergOne neg neg neg) (A.heisenbergOne neg pos zer) = refl
nativeToWeil_compose (A.heisenbergOne neg neg neg) (A.heisenbergOne neg pos pos) = refl
nativeToWeil_compose (A.heisenbergOne neg neg neg) (A.heisenbergOne zer neg neg) = refl
nativeToWeil_compose (A.heisenbergOne neg neg neg) (A.heisenbergOne zer neg zer) = refl
nativeToWeil_compose (A.heisenbergOne neg neg neg) (A.heisenbergOne zer neg pos) = refl
nativeToWeil_compose (A.heisenbergOne neg neg neg) (A.heisenbergOne zer zer neg) = refl
nativeToWeil_compose (A.heisenbergOne neg neg neg) (A.heisenbergOne zer zer zer) = refl
nativeToWeil_compose (A.heisenbergOne neg neg neg) (A.heisenbergOne zer zer pos) = refl
nativeToWeil_compose (A.heisenbergOne neg neg neg) (A.heisenbergOne zer pos neg) = refl
nativeToWeil_compose (A.heisenbergOne neg neg neg) (A.heisenbergOne zer pos zer) = refl
nativeToWeil_compose (A.heisenbergOne neg neg neg) (A.heisenbergOne zer pos pos) = refl
nativeToWeil_compose (A.heisenbergOne neg neg neg) (A.heisenbergOne pos neg neg) = refl
nativeToWeil_compose (A.heisenbergOne neg neg neg) (A.heisenbergOne pos neg zer) = refl
nativeToWeil_compose (A.heisenbergOne neg neg neg) (A.heisenbergOne pos neg pos) = refl
nativeToWeil_compose (A.heisenbergOne neg neg neg) (A.heisenbergOne pos zer neg) = refl
nativeToWeil_compose (A.heisenbergOne neg neg neg) (A.heisenbergOne pos zer zer) = refl
nativeToWeil_compose (A.heisenbergOne neg neg neg) (A.heisenbergOne pos zer pos) = refl
nativeToWeil_compose (A.heisenbergOne neg neg neg) (A.heisenbergOne pos pos neg) = refl
nativeToWeil_compose (A.heisenbergOne neg neg neg) (A.heisenbergOne pos pos zer) = refl
nativeToWeil_compose (A.heisenbergOne neg neg neg) (A.heisenbergOne pos pos pos) = refl
nativeToWeil_compose (A.heisenbergOne neg neg zer) (A.heisenbergOne neg neg neg) = refl
nativeToWeil_compose (A.heisenbergOne neg neg zer) (A.heisenbergOne neg neg zer) = refl
nativeToWeil_compose (A.heisenbergOne neg neg zer) (A.heisenbergOne neg neg pos) = refl
nativeToWeil_compose (A.heisenbergOne neg neg zer) (A.heisenbergOne neg zer neg) = refl
nativeToWeil_compose (A.heisenbergOne neg neg zer) (A.heisenbergOne neg zer zer) = refl
nativeToWeil_compose (A.heisenbergOne neg neg zer) (A.heisenbergOne neg zer pos) = refl
nativeToWeil_compose (A.heisenbergOne neg neg zer) (A.heisenbergOne neg pos neg) = refl
nativeToWeil_compose (A.heisenbergOne neg neg zer) (A.heisenbergOne neg pos zer) = refl
nativeToWeil_compose (A.heisenbergOne neg neg zer) (A.heisenbergOne neg pos pos) = refl
nativeToWeil_compose (A.heisenbergOne neg neg zer) (A.heisenbergOne zer neg neg) = refl
nativeToWeil_compose (A.heisenbergOne neg neg zer) (A.heisenbergOne zer neg zer) = refl
nativeToWeil_compose (A.heisenbergOne neg neg zer) (A.heisenbergOne zer neg pos) = refl
nativeToWeil_compose (A.heisenbergOne neg neg zer) (A.heisenbergOne zer zer neg) = refl
nativeToWeil_compose (A.heisenbergOne neg neg zer) (A.heisenbergOne zer zer zer) = refl
nativeToWeil_compose (A.heisenbergOne neg neg zer) (A.heisenbergOne zer zer pos) = refl
nativeToWeil_compose (A.heisenbergOne neg neg zer) (A.heisenbergOne zer pos neg) = refl
nativeToWeil_compose (A.heisenbergOne neg neg zer) (A.heisenbergOne zer pos zer) = refl
nativeToWeil_compose (A.heisenbergOne neg neg zer) (A.heisenbergOne zer pos pos) = refl
nativeToWeil_compose (A.heisenbergOne neg neg zer) (A.heisenbergOne pos neg neg) = refl
nativeToWeil_compose (A.heisenbergOne neg neg zer) (A.heisenbergOne pos neg zer) = refl
nativeToWeil_compose (A.heisenbergOne neg neg zer) (A.heisenbergOne pos neg pos) = refl
nativeToWeil_compose (A.heisenbergOne neg neg zer) (A.heisenbergOne pos zer neg) = refl
nativeToWeil_compose (A.heisenbergOne neg neg zer) (A.heisenbergOne pos zer zer) = refl
nativeToWeil_compose (A.heisenbergOne neg neg zer) (A.heisenbergOne pos zer pos) = refl
nativeToWeil_compose (A.heisenbergOne neg neg zer) (A.heisenbergOne pos pos neg) = refl
nativeToWeil_compose (A.heisenbergOne neg neg zer) (A.heisenbergOne pos pos zer) = refl
nativeToWeil_compose (A.heisenbergOne neg neg zer) (A.heisenbergOne pos pos pos) = refl
nativeToWeil_compose (A.heisenbergOne neg neg pos) (A.heisenbergOne neg neg neg) = refl
nativeToWeil_compose (A.heisenbergOne neg neg pos) (A.heisenbergOne neg neg zer) = refl
nativeToWeil_compose (A.heisenbergOne neg neg pos) (A.heisenbergOne neg neg pos) = refl
nativeToWeil_compose (A.heisenbergOne neg neg pos) (A.heisenbergOne neg zer neg) = refl
nativeToWeil_compose (A.heisenbergOne neg neg pos) (A.heisenbergOne neg zer zer) = refl
nativeToWeil_compose (A.heisenbergOne neg neg pos) (A.heisenbergOne neg zer pos) = refl
nativeToWeil_compose (A.heisenbergOne neg neg pos) (A.heisenbergOne neg pos neg) = refl
nativeToWeil_compose (A.heisenbergOne neg neg pos) (A.heisenbergOne neg pos zer) = refl
nativeToWeil_compose (A.heisenbergOne neg neg pos) (A.heisenbergOne neg pos pos) = refl
nativeToWeil_compose (A.heisenbergOne neg neg pos) (A.heisenbergOne zer neg neg) = refl
nativeToWeil_compose (A.heisenbergOne neg neg pos) (A.heisenbergOne zer neg zer) = refl
nativeToWeil_compose (A.heisenbergOne neg neg pos) (A.heisenbergOne zer neg pos) = refl
nativeToWeil_compose (A.heisenbergOne neg neg pos) (A.heisenbergOne zer zer neg) = refl
nativeToWeil_compose (A.heisenbergOne neg neg pos) (A.heisenbergOne zer zer zer) = refl
nativeToWeil_compose (A.heisenbergOne neg neg pos) (A.heisenbergOne zer zer pos) = refl
nativeToWeil_compose (A.heisenbergOne neg neg pos) (A.heisenbergOne zer pos neg) = refl
nativeToWeil_compose (A.heisenbergOne neg neg pos) (A.heisenbergOne zer pos zer) = refl
nativeToWeil_compose (A.heisenbergOne neg neg pos) (A.heisenbergOne zer pos pos) = refl
nativeToWeil_compose (A.heisenbergOne neg neg pos) (A.heisenbergOne pos neg neg) = refl
nativeToWeil_compose (A.heisenbergOne neg neg pos) (A.heisenbergOne pos neg zer) = refl
nativeToWeil_compose (A.heisenbergOne neg neg pos) (A.heisenbergOne pos neg pos) = refl
nativeToWeil_compose (A.heisenbergOne neg neg pos) (A.heisenbergOne pos zer neg) = refl
nativeToWeil_compose (A.heisenbergOne neg neg pos) (A.heisenbergOne pos zer zer) = refl
nativeToWeil_compose (A.heisenbergOne neg neg pos) (A.heisenbergOne pos zer pos) = refl
nativeToWeil_compose (A.heisenbergOne neg neg pos) (A.heisenbergOne pos pos neg) = refl
nativeToWeil_compose (A.heisenbergOne neg neg pos) (A.heisenbergOne pos pos zer) = refl
nativeToWeil_compose (A.heisenbergOne neg neg pos) (A.heisenbergOne pos pos pos) = refl
nativeToWeil_compose (A.heisenbergOne neg zer neg) (A.heisenbergOne neg neg neg) = refl
nativeToWeil_compose (A.heisenbergOne neg zer neg) (A.heisenbergOne neg neg zer) = refl
nativeToWeil_compose (A.heisenbergOne neg zer neg) (A.heisenbergOne neg neg pos) = refl
nativeToWeil_compose (A.heisenbergOne neg zer neg) (A.heisenbergOne neg zer neg) = refl
nativeToWeil_compose (A.heisenbergOne neg zer neg) (A.heisenbergOne neg zer zer) = refl
nativeToWeil_compose (A.heisenbergOne neg zer neg) (A.heisenbergOne neg zer pos) = refl
nativeToWeil_compose (A.heisenbergOne neg zer neg) (A.heisenbergOne neg pos neg) = refl
nativeToWeil_compose (A.heisenbergOne neg zer neg) (A.heisenbergOne neg pos zer) = refl
nativeToWeil_compose (A.heisenbergOne neg zer neg) (A.heisenbergOne neg pos pos) = refl
nativeToWeil_compose (A.heisenbergOne neg zer neg) (A.heisenbergOne zer neg neg) = refl
nativeToWeil_compose (A.heisenbergOne neg zer neg) (A.heisenbergOne zer neg zer) = refl
nativeToWeil_compose (A.heisenbergOne neg zer neg) (A.heisenbergOne zer neg pos) = refl
nativeToWeil_compose (A.heisenbergOne neg zer neg) (A.heisenbergOne zer zer neg) = refl
nativeToWeil_compose (A.heisenbergOne neg zer neg) (A.heisenbergOne zer zer zer) = refl
nativeToWeil_compose (A.heisenbergOne neg zer neg) (A.heisenbergOne zer zer pos) = refl
nativeToWeil_compose (A.heisenbergOne neg zer neg) (A.heisenbergOne zer pos neg) = refl
nativeToWeil_compose (A.heisenbergOne neg zer neg) (A.heisenbergOne zer pos zer) = refl
nativeToWeil_compose (A.heisenbergOne neg zer neg) (A.heisenbergOne zer pos pos) = refl
nativeToWeil_compose (A.heisenbergOne neg zer neg) (A.heisenbergOne pos neg neg) = refl
nativeToWeil_compose (A.heisenbergOne neg zer neg) (A.heisenbergOne pos neg zer) = refl
nativeToWeil_compose (A.heisenbergOne neg zer neg) (A.heisenbergOne pos neg pos) = refl
nativeToWeil_compose (A.heisenbergOne neg zer neg) (A.heisenbergOne pos zer neg) = refl
nativeToWeil_compose (A.heisenbergOne neg zer neg) (A.heisenbergOne pos zer zer) = refl
nativeToWeil_compose (A.heisenbergOne neg zer neg) (A.heisenbergOne pos zer pos) = refl
nativeToWeil_compose (A.heisenbergOne neg zer neg) (A.heisenbergOne pos pos neg) = refl
nativeToWeil_compose (A.heisenbergOne neg zer neg) (A.heisenbergOne pos pos zer) = refl
nativeToWeil_compose (A.heisenbergOne neg zer neg) (A.heisenbergOne pos pos pos) = refl
nativeToWeil_compose (A.heisenbergOne neg zer zer) (A.heisenbergOne neg neg neg) = refl
nativeToWeil_compose (A.heisenbergOne neg zer zer) (A.heisenbergOne neg neg zer) = refl
nativeToWeil_compose (A.heisenbergOne neg zer zer) (A.heisenbergOne neg neg pos) = refl
nativeToWeil_compose (A.heisenbergOne neg zer zer) (A.heisenbergOne neg zer neg) = refl
nativeToWeil_compose (A.heisenbergOne neg zer zer) (A.heisenbergOne neg zer zer) = refl
nativeToWeil_compose (A.heisenbergOne neg zer zer) (A.heisenbergOne neg zer pos) = refl
nativeToWeil_compose (A.heisenbergOne neg zer zer) (A.heisenbergOne neg pos neg) = refl
nativeToWeil_compose (A.heisenbergOne neg zer zer) (A.heisenbergOne neg pos zer) = refl
nativeToWeil_compose (A.heisenbergOne neg zer zer) (A.heisenbergOne neg pos pos) = refl
nativeToWeil_compose (A.heisenbergOne neg zer zer) (A.heisenbergOne zer neg neg) = refl
nativeToWeil_compose (A.heisenbergOne neg zer zer) (A.heisenbergOne zer neg zer) = refl
nativeToWeil_compose (A.heisenbergOne neg zer zer) (A.heisenbergOne zer neg pos) = refl
nativeToWeil_compose (A.heisenbergOne neg zer zer) (A.heisenbergOne zer zer neg) = refl
nativeToWeil_compose (A.heisenbergOne neg zer zer) (A.heisenbergOne zer zer zer) = refl
nativeToWeil_compose (A.heisenbergOne neg zer zer) (A.heisenbergOne zer zer pos) = refl
nativeToWeil_compose (A.heisenbergOne neg zer zer) (A.heisenbergOne zer pos neg) = refl
nativeToWeil_compose (A.heisenbergOne neg zer zer) (A.heisenbergOne zer pos zer) = refl
nativeToWeil_compose (A.heisenbergOne neg zer zer) (A.heisenbergOne zer pos pos) = refl
nativeToWeil_compose (A.heisenbergOne neg zer zer) (A.heisenbergOne pos neg neg) = refl
nativeToWeil_compose (A.heisenbergOne neg zer zer) (A.heisenbergOne pos neg zer) = refl
nativeToWeil_compose (A.heisenbergOne neg zer zer) (A.heisenbergOne pos neg pos) = refl
nativeToWeil_compose (A.heisenbergOne neg zer zer) (A.heisenbergOne pos zer neg) = refl
nativeToWeil_compose (A.heisenbergOne neg zer zer) (A.heisenbergOne pos zer zer) = refl
nativeToWeil_compose (A.heisenbergOne neg zer zer) (A.heisenbergOne pos zer pos) = refl
nativeToWeil_compose (A.heisenbergOne neg zer zer) (A.heisenbergOne pos pos neg) = refl
nativeToWeil_compose (A.heisenbergOne neg zer zer) (A.heisenbergOne pos pos zer) = refl
nativeToWeil_compose (A.heisenbergOne neg zer zer) (A.heisenbergOne pos pos pos) = refl
nativeToWeil_compose (A.heisenbergOne neg zer pos) (A.heisenbergOne neg neg neg) = refl
nativeToWeil_compose (A.heisenbergOne neg zer pos) (A.heisenbergOne neg neg zer) = refl
nativeToWeil_compose (A.heisenbergOne neg zer pos) (A.heisenbergOne neg neg pos) = refl
nativeToWeil_compose (A.heisenbergOne neg zer pos) (A.heisenbergOne neg zer neg) = refl
nativeToWeil_compose (A.heisenbergOne neg zer pos) (A.heisenbergOne neg zer zer) = refl
nativeToWeil_compose (A.heisenbergOne neg zer pos) (A.heisenbergOne neg zer pos) = refl
nativeToWeil_compose (A.heisenbergOne neg zer pos) (A.heisenbergOne neg pos neg) = refl
nativeToWeil_compose (A.heisenbergOne neg zer pos) (A.heisenbergOne neg pos zer) = refl
nativeToWeil_compose (A.heisenbergOne neg zer pos) (A.heisenbergOne neg pos pos) = refl
nativeToWeil_compose (A.heisenbergOne neg zer pos) (A.heisenbergOne zer neg neg) = refl
nativeToWeil_compose (A.heisenbergOne neg zer pos) (A.heisenbergOne zer neg zer) = refl
nativeToWeil_compose (A.heisenbergOne neg zer pos) (A.heisenbergOne zer neg pos) = refl
nativeToWeil_compose (A.heisenbergOne neg zer pos) (A.heisenbergOne zer zer neg) = refl
nativeToWeil_compose (A.heisenbergOne neg zer pos) (A.heisenbergOne zer zer zer) = refl
nativeToWeil_compose (A.heisenbergOne neg zer pos) (A.heisenbergOne zer zer pos) = refl
nativeToWeil_compose (A.heisenbergOne neg zer pos) (A.heisenbergOne zer pos neg) = refl
nativeToWeil_compose (A.heisenbergOne neg zer pos) (A.heisenbergOne zer pos zer) = refl
nativeToWeil_compose (A.heisenbergOne neg zer pos) (A.heisenbergOne zer pos pos) = refl
nativeToWeil_compose (A.heisenbergOne neg zer pos) (A.heisenbergOne pos neg neg) = refl
nativeToWeil_compose (A.heisenbergOne neg zer pos) (A.heisenbergOne pos neg zer) = refl
nativeToWeil_compose (A.heisenbergOne neg zer pos) (A.heisenbergOne pos neg pos) = refl
nativeToWeil_compose (A.heisenbergOne neg zer pos) (A.heisenbergOne pos zer neg) = refl
nativeToWeil_compose (A.heisenbergOne neg zer pos) (A.heisenbergOne pos zer zer) = refl
nativeToWeil_compose (A.heisenbergOne neg zer pos) (A.heisenbergOne pos zer pos) = refl
nativeToWeil_compose (A.heisenbergOne neg zer pos) (A.heisenbergOne pos pos neg) = refl
nativeToWeil_compose (A.heisenbergOne neg zer pos) (A.heisenbergOne pos pos zer) = refl
nativeToWeil_compose (A.heisenbergOne neg zer pos) (A.heisenbergOne pos pos pos) = refl
nativeToWeil_compose (A.heisenbergOne neg pos neg) (A.heisenbergOne neg neg neg) = refl
nativeToWeil_compose (A.heisenbergOne neg pos neg) (A.heisenbergOne neg neg zer) = refl
nativeToWeil_compose (A.heisenbergOne neg pos neg) (A.heisenbergOne neg neg pos) = refl
nativeToWeil_compose (A.heisenbergOne neg pos neg) (A.heisenbergOne neg zer neg) = refl
nativeToWeil_compose (A.heisenbergOne neg pos neg) (A.heisenbergOne neg zer zer) = refl
nativeToWeil_compose (A.heisenbergOne neg pos neg) (A.heisenbergOne neg zer pos) = refl
nativeToWeil_compose (A.heisenbergOne neg pos neg) (A.heisenbergOne neg pos neg) = refl
nativeToWeil_compose (A.heisenbergOne neg pos neg) (A.heisenbergOne neg pos zer) = refl
nativeToWeil_compose (A.heisenbergOne neg pos neg) (A.heisenbergOne neg pos pos) = refl
nativeToWeil_compose (A.heisenbergOne neg pos neg) (A.heisenbergOne zer neg neg) = refl
nativeToWeil_compose (A.heisenbergOne neg pos neg) (A.heisenbergOne zer neg zer) = refl
nativeToWeil_compose (A.heisenbergOne neg pos neg) (A.heisenbergOne zer neg pos) = refl
nativeToWeil_compose (A.heisenbergOne neg pos neg) (A.heisenbergOne zer zer neg) = refl
nativeToWeil_compose (A.heisenbergOne neg pos neg) (A.heisenbergOne zer zer zer) = refl
nativeToWeil_compose (A.heisenbergOne neg pos neg) (A.heisenbergOne zer zer pos) = refl
nativeToWeil_compose (A.heisenbergOne neg pos neg) (A.heisenbergOne zer pos neg) = refl
nativeToWeil_compose (A.heisenbergOne neg pos neg) (A.heisenbergOne zer pos zer) = refl
nativeToWeil_compose (A.heisenbergOne neg pos neg) (A.heisenbergOne zer pos pos) = refl
nativeToWeil_compose (A.heisenbergOne neg pos neg) (A.heisenbergOne pos neg neg) = refl
nativeToWeil_compose (A.heisenbergOne neg pos neg) (A.heisenbergOne pos neg zer) = refl
nativeToWeil_compose (A.heisenbergOne neg pos neg) (A.heisenbergOne pos neg pos) = refl
nativeToWeil_compose (A.heisenbergOne neg pos neg) (A.heisenbergOne pos zer neg) = refl
nativeToWeil_compose (A.heisenbergOne neg pos neg) (A.heisenbergOne pos zer zer) = refl
nativeToWeil_compose (A.heisenbergOne neg pos neg) (A.heisenbergOne pos zer pos) = refl
nativeToWeil_compose (A.heisenbergOne neg pos neg) (A.heisenbergOne pos pos neg) = refl
nativeToWeil_compose (A.heisenbergOne neg pos neg) (A.heisenbergOne pos pos zer) = refl
nativeToWeil_compose (A.heisenbergOne neg pos neg) (A.heisenbergOne pos pos pos) = refl
nativeToWeil_compose (A.heisenbergOne neg pos zer) (A.heisenbergOne neg neg neg) = refl
nativeToWeil_compose (A.heisenbergOne neg pos zer) (A.heisenbergOne neg neg zer) = refl
nativeToWeil_compose (A.heisenbergOne neg pos zer) (A.heisenbergOne neg neg pos) = refl
nativeToWeil_compose (A.heisenbergOne neg pos zer) (A.heisenbergOne neg zer neg) = refl
nativeToWeil_compose (A.heisenbergOne neg pos zer) (A.heisenbergOne neg zer zer) = refl
nativeToWeil_compose (A.heisenbergOne neg pos zer) (A.heisenbergOne neg zer pos) = refl
nativeToWeil_compose (A.heisenbergOne neg pos zer) (A.heisenbergOne neg pos neg) = refl
nativeToWeil_compose (A.heisenbergOne neg pos zer) (A.heisenbergOne neg pos zer) = refl
nativeToWeil_compose (A.heisenbergOne neg pos zer) (A.heisenbergOne neg pos pos) = refl
nativeToWeil_compose (A.heisenbergOne neg pos zer) (A.heisenbergOne zer neg neg) = refl
nativeToWeil_compose (A.heisenbergOne neg pos zer) (A.heisenbergOne zer neg zer) = refl
nativeToWeil_compose (A.heisenbergOne neg pos zer) (A.heisenbergOne zer neg pos) = refl
nativeToWeil_compose (A.heisenbergOne neg pos zer) (A.heisenbergOne zer zer neg) = refl
nativeToWeil_compose (A.heisenbergOne neg pos zer) (A.heisenbergOne zer zer zer) = refl
nativeToWeil_compose (A.heisenbergOne neg pos zer) (A.heisenbergOne zer zer pos) = refl
nativeToWeil_compose (A.heisenbergOne neg pos zer) (A.heisenbergOne zer pos neg) = refl
nativeToWeil_compose (A.heisenbergOne neg pos zer) (A.heisenbergOne zer pos zer) = refl
nativeToWeil_compose (A.heisenbergOne neg pos zer) (A.heisenbergOne zer pos pos) = refl
nativeToWeil_compose (A.heisenbergOne neg pos zer) (A.heisenbergOne pos neg neg) = refl
nativeToWeil_compose (A.heisenbergOne neg pos zer) (A.heisenbergOne pos neg zer) = refl
nativeToWeil_compose (A.heisenbergOne neg pos zer) (A.heisenbergOne pos neg pos) = refl
nativeToWeil_compose (A.heisenbergOne neg pos zer) (A.heisenbergOne pos zer neg) = refl
nativeToWeil_compose (A.heisenbergOne neg pos zer) (A.heisenbergOne pos zer zer) = refl
nativeToWeil_compose (A.heisenbergOne neg pos zer) (A.heisenbergOne pos zer pos) = refl
nativeToWeil_compose (A.heisenbergOne neg pos zer) (A.heisenbergOne pos pos neg) = refl
nativeToWeil_compose (A.heisenbergOne neg pos zer) (A.heisenbergOne pos pos zer) = refl
nativeToWeil_compose (A.heisenbergOne neg pos zer) (A.heisenbergOne pos pos pos) = refl
nativeToWeil_compose (A.heisenbergOne neg pos pos) (A.heisenbergOne neg neg neg) = refl
nativeToWeil_compose (A.heisenbergOne neg pos pos) (A.heisenbergOne neg neg zer) = refl
nativeToWeil_compose (A.heisenbergOne neg pos pos) (A.heisenbergOne neg neg pos) = refl
nativeToWeil_compose (A.heisenbergOne neg pos pos) (A.heisenbergOne neg zer neg) = refl
nativeToWeil_compose (A.heisenbergOne neg pos pos) (A.heisenbergOne neg zer zer) = refl
nativeToWeil_compose (A.heisenbergOne neg pos pos) (A.heisenbergOne neg zer pos) = refl
nativeToWeil_compose (A.heisenbergOne neg pos pos) (A.heisenbergOne neg pos neg) = refl
nativeToWeil_compose (A.heisenbergOne neg pos pos) (A.heisenbergOne neg pos zer) = refl
nativeToWeil_compose (A.heisenbergOne neg pos pos) (A.heisenbergOne neg pos pos) = refl
nativeToWeil_compose (A.heisenbergOne neg pos pos) (A.heisenbergOne zer neg neg) = refl
nativeToWeil_compose (A.heisenbergOne neg pos pos) (A.heisenbergOne zer neg zer) = refl
nativeToWeil_compose (A.heisenbergOne neg pos pos) (A.heisenbergOne zer neg pos) = refl
nativeToWeil_compose (A.heisenbergOne neg pos pos) (A.heisenbergOne zer zer neg) = refl
nativeToWeil_compose (A.heisenbergOne neg pos pos) (A.heisenbergOne zer zer zer) = refl
nativeToWeil_compose (A.heisenbergOne neg pos pos) (A.heisenbergOne zer zer pos) = refl
nativeToWeil_compose (A.heisenbergOne neg pos pos) (A.heisenbergOne zer pos neg) = refl
nativeToWeil_compose (A.heisenbergOne neg pos pos) (A.heisenbergOne zer pos zer) = refl
nativeToWeil_compose (A.heisenbergOne neg pos pos) (A.heisenbergOne zer pos pos) = refl
nativeToWeil_compose (A.heisenbergOne neg pos pos) (A.heisenbergOne pos neg neg) = refl
nativeToWeil_compose (A.heisenbergOne neg pos pos) (A.heisenbergOne pos neg zer) = refl
nativeToWeil_compose (A.heisenbergOne neg pos pos) (A.heisenbergOne pos neg pos) = refl
nativeToWeil_compose (A.heisenbergOne neg pos pos) (A.heisenbergOne pos zer neg) = refl
nativeToWeil_compose (A.heisenbergOne neg pos pos) (A.heisenbergOne pos zer zer) = refl
nativeToWeil_compose (A.heisenbergOne neg pos pos) (A.heisenbergOne pos zer pos) = refl
nativeToWeil_compose (A.heisenbergOne neg pos pos) (A.heisenbergOne pos pos neg) = refl
nativeToWeil_compose (A.heisenbergOne neg pos pos) (A.heisenbergOne pos pos zer) = refl
nativeToWeil_compose (A.heisenbergOne neg pos pos) (A.heisenbergOne pos pos pos) = refl
nativeToWeil_compose (A.heisenbergOne zer neg neg) (A.heisenbergOne neg neg neg) = refl
nativeToWeil_compose (A.heisenbergOne zer neg neg) (A.heisenbergOne neg neg zer) = refl
nativeToWeil_compose (A.heisenbergOne zer neg neg) (A.heisenbergOne neg neg pos) = refl
nativeToWeil_compose (A.heisenbergOne zer neg neg) (A.heisenbergOne neg zer neg) = refl
nativeToWeil_compose (A.heisenbergOne zer neg neg) (A.heisenbergOne neg zer zer) = refl
nativeToWeil_compose (A.heisenbergOne zer neg neg) (A.heisenbergOne neg zer pos) = refl
nativeToWeil_compose (A.heisenbergOne zer neg neg) (A.heisenbergOne neg pos neg) = refl
nativeToWeil_compose (A.heisenbergOne zer neg neg) (A.heisenbergOne neg pos zer) = refl
nativeToWeil_compose (A.heisenbergOne zer neg neg) (A.heisenbergOne neg pos pos) = refl
nativeToWeil_compose (A.heisenbergOne zer neg neg) (A.heisenbergOne zer neg neg) = refl
nativeToWeil_compose (A.heisenbergOne zer neg neg) (A.heisenbergOne zer neg zer) = refl
nativeToWeil_compose (A.heisenbergOne zer neg neg) (A.heisenbergOne zer neg pos) = refl
nativeToWeil_compose (A.heisenbergOne zer neg neg) (A.heisenbergOne zer zer neg) = refl
nativeToWeil_compose (A.heisenbergOne zer neg neg) (A.heisenbergOne zer zer zer) = refl
nativeToWeil_compose (A.heisenbergOne zer neg neg) (A.heisenbergOne zer zer pos) = refl
nativeToWeil_compose (A.heisenbergOne zer neg neg) (A.heisenbergOne zer pos neg) = refl
nativeToWeil_compose (A.heisenbergOne zer neg neg) (A.heisenbergOne zer pos zer) = refl
nativeToWeil_compose (A.heisenbergOne zer neg neg) (A.heisenbergOne zer pos pos) = refl
nativeToWeil_compose (A.heisenbergOne zer neg neg) (A.heisenbergOne pos neg neg) = refl
nativeToWeil_compose (A.heisenbergOne zer neg neg) (A.heisenbergOne pos neg zer) = refl
nativeToWeil_compose (A.heisenbergOne zer neg neg) (A.heisenbergOne pos neg pos) = refl
nativeToWeil_compose (A.heisenbergOne zer neg neg) (A.heisenbergOne pos zer neg) = refl
nativeToWeil_compose (A.heisenbergOne zer neg neg) (A.heisenbergOne pos zer zer) = refl
nativeToWeil_compose (A.heisenbergOne zer neg neg) (A.heisenbergOne pos zer pos) = refl
nativeToWeil_compose (A.heisenbergOne zer neg neg) (A.heisenbergOne pos pos neg) = refl
nativeToWeil_compose (A.heisenbergOne zer neg neg) (A.heisenbergOne pos pos zer) = refl
nativeToWeil_compose (A.heisenbergOne zer neg neg) (A.heisenbergOne pos pos pos) = refl
nativeToWeil_compose (A.heisenbergOne zer neg zer) (A.heisenbergOne neg neg neg) = refl
nativeToWeil_compose (A.heisenbergOne zer neg zer) (A.heisenbergOne neg neg zer) = refl
nativeToWeil_compose (A.heisenbergOne zer neg zer) (A.heisenbergOne neg neg pos) = refl
nativeToWeil_compose (A.heisenbergOne zer neg zer) (A.heisenbergOne neg zer neg) = refl
nativeToWeil_compose (A.heisenbergOne zer neg zer) (A.heisenbergOne neg zer zer) = refl
nativeToWeil_compose (A.heisenbergOne zer neg zer) (A.heisenbergOne neg zer pos) = refl
nativeToWeil_compose (A.heisenbergOne zer neg zer) (A.heisenbergOne neg pos neg) = refl
nativeToWeil_compose (A.heisenbergOne zer neg zer) (A.heisenbergOne neg pos zer) = refl
nativeToWeil_compose (A.heisenbergOne zer neg zer) (A.heisenbergOne neg pos pos) = refl
nativeToWeil_compose (A.heisenbergOne zer neg zer) (A.heisenbergOne zer neg neg) = refl
nativeToWeil_compose (A.heisenbergOne zer neg zer) (A.heisenbergOne zer neg zer) = refl
nativeToWeil_compose (A.heisenbergOne zer neg zer) (A.heisenbergOne zer neg pos) = refl
nativeToWeil_compose (A.heisenbergOne zer neg zer) (A.heisenbergOne zer zer neg) = refl
nativeToWeil_compose (A.heisenbergOne zer neg zer) (A.heisenbergOne zer zer zer) = refl
nativeToWeil_compose (A.heisenbergOne zer neg zer) (A.heisenbergOne zer zer pos) = refl
nativeToWeil_compose (A.heisenbergOne zer neg zer) (A.heisenbergOne zer pos neg) = refl
nativeToWeil_compose (A.heisenbergOne zer neg zer) (A.heisenbergOne zer pos zer) = refl
nativeToWeil_compose (A.heisenbergOne zer neg zer) (A.heisenbergOne zer pos pos) = refl
nativeToWeil_compose (A.heisenbergOne zer neg zer) (A.heisenbergOne pos neg neg) = refl
nativeToWeil_compose (A.heisenbergOne zer neg zer) (A.heisenbergOne pos neg zer) = refl
nativeToWeil_compose (A.heisenbergOne zer neg zer) (A.heisenbergOne pos neg pos) = refl
nativeToWeil_compose (A.heisenbergOne zer neg zer) (A.heisenbergOne pos zer neg) = refl
nativeToWeil_compose (A.heisenbergOne zer neg zer) (A.heisenbergOne pos zer zer) = refl
nativeToWeil_compose (A.heisenbergOne zer neg zer) (A.heisenbergOne pos zer pos) = refl
nativeToWeil_compose (A.heisenbergOne zer neg zer) (A.heisenbergOne pos pos neg) = refl
nativeToWeil_compose (A.heisenbergOne zer neg zer) (A.heisenbergOne pos pos zer) = refl
nativeToWeil_compose (A.heisenbergOne zer neg zer) (A.heisenbergOne pos pos pos) = refl
nativeToWeil_compose (A.heisenbergOne zer neg pos) (A.heisenbergOne neg neg neg) = refl
nativeToWeil_compose (A.heisenbergOne zer neg pos) (A.heisenbergOne neg neg zer) = refl
nativeToWeil_compose (A.heisenbergOne zer neg pos) (A.heisenbergOne neg neg pos) = refl
nativeToWeil_compose (A.heisenbergOne zer neg pos) (A.heisenbergOne neg zer neg) = refl
nativeToWeil_compose (A.heisenbergOne zer neg pos) (A.heisenbergOne neg zer zer) = refl
nativeToWeil_compose (A.heisenbergOne zer neg pos) (A.heisenbergOne neg zer pos) = refl
nativeToWeil_compose (A.heisenbergOne zer neg pos) (A.heisenbergOne neg pos neg) = refl
nativeToWeil_compose (A.heisenbergOne zer neg pos) (A.heisenbergOne neg pos zer) = refl
nativeToWeil_compose (A.heisenbergOne zer neg pos) (A.heisenbergOne neg pos pos) = refl
nativeToWeil_compose (A.heisenbergOne zer neg pos) (A.heisenbergOne zer neg neg) = refl
nativeToWeil_compose (A.heisenbergOne zer neg pos) (A.heisenbergOne zer neg zer) = refl
nativeToWeil_compose (A.heisenbergOne zer neg pos) (A.heisenbergOne zer neg pos) = refl
nativeToWeil_compose (A.heisenbergOne zer neg pos) (A.heisenbergOne zer zer neg) = refl
nativeToWeil_compose (A.heisenbergOne zer neg pos) (A.heisenbergOne zer zer zer) = refl
nativeToWeil_compose (A.heisenbergOne zer neg pos) (A.heisenbergOne zer zer pos) = refl
nativeToWeil_compose (A.heisenbergOne zer neg pos) (A.heisenbergOne zer pos neg) = refl
nativeToWeil_compose (A.heisenbergOne zer neg pos) (A.heisenbergOne zer pos zer) = refl
nativeToWeil_compose (A.heisenbergOne zer neg pos) (A.heisenbergOne zer pos pos) = refl
nativeToWeil_compose (A.heisenbergOne zer neg pos) (A.heisenbergOne pos neg neg) = refl
nativeToWeil_compose (A.heisenbergOne zer neg pos) (A.heisenbergOne pos neg zer) = refl
nativeToWeil_compose (A.heisenbergOne zer neg pos) (A.heisenbergOne pos neg pos) = refl
nativeToWeil_compose (A.heisenbergOne zer neg pos) (A.heisenbergOne pos zer neg) = refl
nativeToWeil_compose (A.heisenbergOne zer neg pos) (A.heisenbergOne pos zer zer) = refl
nativeToWeil_compose (A.heisenbergOne zer neg pos) (A.heisenbergOne pos zer pos) = refl
nativeToWeil_compose (A.heisenbergOne zer neg pos) (A.heisenbergOne pos pos neg) = refl
nativeToWeil_compose (A.heisenbergOne zer neg pos) (A.heisenbergOne pos pos zer) = refl
nativeToWeil_compose (A.heisenbergOne zer neg pos) (A.heisenbergOne pos pos pos) = refl
nativeToWeil_compose (A.heisenbergOne zer zer neg) (A.heisenbergOne neg neg neg) = refl
nativeToWeil_compose (A.heisenbergOne zer zer neg) (A.heisenbergOne neg neg zer) = refl
nativeToWeil_compose (A.heisenbergOne zer zer neg) (A.heisenbergOne neg neg pos) = refl
nativeToWeil_compose (A.heisenbergOne zer zer neg) (A.heisenbergOne neg zer neg) = refl
nativeToWeil_compose (A.heisenbergOne zer zer neg) (A.heisenbergOne neg zer zer) = refl
nativeToWeil_compose (A.heisenbergOne zer zer neg) (A.heisenbergOne neg zer pos) = refl
nativeToWeil_compose (A.heisenbergOne zer zer neg) (A.heisenbergOne neg pos neg) = refl
nativeToWeil_compose (A.heisenbergOne zer zer neg) (A.heisenbergOne neg pos zer) = refl
nativeToWeil_compose (A.heisenbergOne zer zer neg) (A.heisenbergOne neg pos pos) = refl
nativeToWeil_compose (A.heisenbergOne zer zer neg) (A.heisenbergOne zer neg neg) = refl
nativeToWeil_compose (A.heisenbergOne zer zer neg) (A.heisenbergOne zer neg zer) = refl
nativeToWeil_compose (A.heisenbergOne zer zer neg) (A.heisenbergOne zer neg pos) = refl
nativeToWeil_compose (A.heisenbergOne zer zer neg) (A.heisenbergOne zer zer neg) = refl
nativeToWeil_compose (A.heisenbergOne zer zer neg) (A.heisenbergOne zer zer zer) = refl
nativeToWeil_compose (A.heisenbergOne zer zer neg) (A.heisenbergOne zer zer pos) = refl
nativeToWeil_compose (A.heisenbergOne zer zer neg) (A.heisenbergOne zer pos neg) = refl
nativeToWeil_compose (A.heisenbergOne zer zer neg) (A.heisenbergOne zer pos zer) = refl
nativeToWeil_compose (A.heisenbergOne zer zer neg) (A.heisenbergOne zer pos pos) = refl
nativeToWeil_compose (A.heisenbergOne zer zer neg) (A.heisenbergOne pos neg neg) = refl
nativeToWeil_compose (A.heisenbergOne zer zer neg) (A.heisenbergOne pos neg zer) = refl
nativeToWeil_compose (A.heisenbergOne zer zer neg) (A.heisenbergOne pos neg pos) = refl
nativeToWeil_compose (A.heisenbergOne zer zer neg) (A.heisenbergOne pos zer neg) = refl
nativeToWeil_compose (A.heisenbergOne zer zer neg) (A.heisenbergOne pos zer zer) = refl
nativeToWeil_compose (A.heisenbergOne zer zer neg) (A.heisenbergOne pos zer pos) = refl
nativeToWeil_compose (A.heisenbergOne zer zer neg) (A.heisenbergOne pos pos neg) = refl
nativeToWeil_compose (A.heisenbergOne zer zer neg) (A.heisenbergOne pos pos zer) = refl
nativeToWeil_compose (A.heisenbergOne zer zer neg) (A.heisenbergOne pos pos pos) = refl
nativeToWeil_compose (A.heisenbergOne zer zer zer) (A.heisenbergOne neg neg neg) = refl
nativeToWeil_compose (A.heisenbergOne zer zer zer) (A.heisenbergOne neg neg zer) = refl
nativeToWeil_compose (A.heisenbergOne zer zer zer) (A.heisenbergOne neg neg pos) = refl
nativeToWeil_compose (A.heisenbergOne zer zer zer) (A.heisenbergOne neg zer neg) = refl
nativeToWeil_compose (A.heisenbergOne zer zer zer) (A.heisenbergOne neg zer zer) = refl
nativeToWeil_compose (A.heisenbergOne zer zer zer) (A.heisenbergOne neg zer pos) = refl
nativeToWeil_compose (A.heisenbergOne zer zer zer) (A.heisenbergOne neg pos neg) = refl
nativeToWeil_compose (A.heisenbergOne zer zer zer) (A.heisenbergOne neg pos zer) = refl
nativeToWeil_compose (A.heisenbergOne zer zer zer) (A.heisenbergOne neg pos pos) = refl
nativeToWeil_compose (A.heisenbergOne zer zer zer) (A.heisenbergOne zer neg neg) = refl
nativeToWeil_compose (A.heisenbergOne zer zer zer) (A.heisenbergOne zer neg zer) = refl
nativeToWeil_compose (A.heisenbergOne zer zer zer) (A.heisenbergOne zer neg pos) = refl
nativeToWeil_compose (A.heisenbergOne zer zer zer) (A.heisenbergOne zer zer neg) = refl
nativeToWeil_compose (A.heisenbergOne zer zer zer) (A.heisenbergOne zer zer zer) = refl
nativeToWeil_compose (A.heisenbergOne zer zer zer) (A.heisenbergOne zer zer pos) = refl
nativeToWeil_compose (A.heisenbergOne zer zer zer) (A.heisenbergOne zer pos neg) = refl
nativeToWeil_compose (A.heisenbergOne zer zer zer) (A.heisenbergOne zer pos zer) = refl
nativeToWeil_compose (A.heisenbergOne zer zer zer) (A.heisenbergOne zer pos pos) = refl
nativeToWeil_compose (A.heisenbergOne zer zer zer) (A.heisenbergOne pos neg neg) = refl
nativeToWeil_compose (A.heisenbergOne zer zer zer) (A.heisenbergOne pos neg zer) = refl
nativeToWeil_compose (A.heisenbergOne zer zer zer) (A.heisenbergOne pos neg pos) = refl
nativeToWeil_compose (A.heisenbergOne zer zer zer) (A.heisenbergOne pos zer neg) = refl
nativeToWeil_compose (A.heisenbergOne zer zer zer) (A.heisenbergOne pos zer zer) = refl
nativeToWeil_compose (A.heisenbergOne zer zer zer) (A.heisenbergOne pos zer pos) = refl
nativeToWeil_compose (A.heisenbergOne zer zer zer) (A.heisenbergOne pos pos neg) = refl
nativeToWeil_compose (A.heisenbergOne zer zer zer) (A.heisenbergOne pos pos zer) = refl
nativeToWeil_compose (A.heisenbergOne zer zer zer) (A.heisenbergOne pos pos pos) = refl
nativeToWeil_compose (A.heisenbergOne zer zer pos) (A.heisenbergOne neg neg neg) = refl
nativeToWeil_compose (A.heisenbergOne zer zer pos) (A.heisenbergOne neg neg zer) = refl
nativeToWeil_compose (A.heisenbergOne zer zer pos) (A.heisenbergOne neg neg pos) = refl
nativeToWeil_compose (A.heisenbergOne zer zer pos) (A.heisenbergOne neg zer neg) = refl
nativeToWeil_compose (A.heisenbergOne zer zer pos) (A.heisenbergOne neg zer zer) = refl
nativeToWeil_compose (A.heisenbergOne zer zer pos) (A.heisenbergOne neg zer pos) = refl
nativeToWeil_compose (A.heisenbergOne zer zer pos) (A.heisenbergOne neg pos neg) = refl
nativeToWeil_compose (A.heisenbergOne zer zer pos) (A.heisenbergOne neg pos zer) = refl
nativeToWeil_compose (A.heisenbergOne zer zer pos) (A.heisenbergOne neg pos pos) = refl
nativeToWeil_compose (A.heisenbergOne zer zer pos) (A.heisenbergOne zer neg neg) = refl
nativeToWeil_compose (A.heisenbergOne zer zer pos) (A.heisenbergOne zer neg zer) = refl
nativeToWeil_compose (A.heisenbergOne zer zer pos) (A.heisenbergOne zer neg pos) = refl
nativeToWeil_compose (A.heisenbergOne zer zer pos) (A.heisenbergOne zer zer neg) = refl
nativeToWeil_compose (A.heisenbergOne zer zer pos) (A.heisenbergOne zer zer zer) = refl
nativeToWeil_compose (A.heisenbergOne zer zer pos) (A.heisenbergOne zer zer pos) = refl
nativeToWeil_compose (A.heisenbergOne zer zer pos) (A.heisenbergOne zer pos neg) = refl
nativeToWeil_compose (A.heisenbergOne zer zer pos) (A.heisenbergOne zer pos zer) = refl
nativeToWeil_compose (A.heisenbergOne zer zer pos) (A.heisenbergOne zer pos pos) = refl
nativeToWeil_compose (A.heisenbergOne zer zer pos) (A.heisenbergOne pos neg neg) = refl
nativeToWeil_compose (A.heisenbergOne zer zer pos) (A.heisenbergOne pos neg zer) = refl
nativeToWeil_compose (A.heisenbergOne zer zer pos) (A.heisenbergOne pos neg pos) = refl
nativeToWeil_compose (A.heisenbergOne zer zer pos) (A.heisenbergOne pos zer neg) = refl
nativeToWeil_compose (A.heisenbergOne zer zer pos) (A.heisenbergOne pos zer zer) = refl
nativeToWeil_compose (A.heisenbergOne zer zer pos) (A.heisenbergOne pos zer pos) = refl
nativeToWeil_compose (A.heisenbergOne zer zer pos) (A.heisenbergOne pos pos neg) = refl
nativeToWeil_compose (A.heisenbergOne zer zer pos) (A.heisenbergOne pos pos zer) = refl
nativeToWeil_compose (A.heisenbergOne zer zer pos) (A.heisenbergOne pos pos pos) = refl
nativeToWeil_compose (A.heisenbergOne zer pos neg) (A.heisenbergOne neg neg neg) = refl
nativeToWeil_compose (A.heisenbergOne zer pos neg) (A.heisenbergOne neg neg zer) = refl
nativeToWeil_compose (A.heisenbergOne zer pos neg) (A.heisenbergOne neg neg pos) = refl
nativeToWeil_compose (A.heisenbergOne zer pos neg) (A.heisenbergOne neg zer neg) = refl
nativeToWeil_compose (A.heisenbergOne zer pos neg) (A.heisenbergOne neg zer zer) = refl
nativeToWeil_compose (A.heisenbergOne zer pos neg) (A.heisenbergOne neg zer pos) = refl
nativeToWeil_compose (A.heisenbergOne zer pos neg) (A.heisenbergOne neg pos neg) = refl
nativeToWeil_compose (A.heisenbergOne zer pos neg) (A.heisenbergOne neg pos zer) = refl
nativeToWeil_compose (A.heisenbergOne zer pos neg) (A.heisenbergOne neg pos pos) = refl
nativeToWeil_compose (A.heisenbergOne zer pos neg) (A.heisenbergOne zer neg neg) = refl
nativeToWeil_compose (A.heisenbergOne zer pos neg) (A.heisenbergOne zer neg zer) = refl
nativeToWeil_compose (A.heisenbergOne zer pos neg) (A.heisenbergOne zer neg pos) = refl
nativeToWeil_compose (A.heisenbergOne zer pos neg) (A.heisenbergOne zer zer neg) = refl
nativeToWeil_compose (A.heisenbergOne zer pos neg) (A.heisenbergOne zer zer zer) = refl
nativeToWeil_compose (A.heisenbergOne zer pos neg) (A.heisenbergOne zer zer pos) = refl
nativeToWeil_compose (A.heisenbergOne zer pos neg) (A.heisenbergOne zer pos neg) = refl
nativeToWeil_compose (A.heisenbergOne zer pos neg) (A.heisenbergOne zer pos zer) = refl
nativeToWeil_compose (A.heisenbergOne zer pos neg) (A.heisenbergOne zer pos pos) = refl
nativeToWeil_compose (A.heisenbergOne zer pos neg) (A.heisenbergOne pos neg neg) = refl
nativeToWeil_compose (A.heisenbergOne zer pos neg) (A.heisenbergOne pos neg zer) = refl
nativeToWeil_compose (A.heisenbergOne zer pos neg) (A.heisenbergOne pos neg pos) = refl
nativeToWeil_compose (A.heisenbergOne zer pos neg) (A.heisenbergOne pos zer neg) = refl
nativeToWeil_compose (A.heisenbergOne zer pos neg) (A.heisenbergOne pos zer zer) = refl
nativeToWeil_compose (A.heisenbergOne zer pos neg) (A.heisenbergOne pos zer pos) = refl
nativeToWeil_compose (A.heisenbergOne zer pos neg) (A.heisenbergOne pos pos neg) = refl
nativeToWeil_compose (A.heisenbergOne zer pos neg) (A.heisenbergOne pos pos zer) = refl
nativeToWeil_compose (A.heisenbergOne zer pos neg) (A.heisenbergOne pos pos pos) = refl
nativeToWeil_compose (A.heisenbergOne zer pos zer) (A.heisenbergOne neg neg neg) = refl
nativeToWeil_compose (A.heisenbergOne zer pos zer) (A.heisenbergOne neg neg zer) = refl
nativeToWeil_compose (A.heisenbergOne zer pos zer) (A.heisenbergOne neg neg pos) = refl
nativeToWeil_compose (A.heisenbergOne zer pos zer) (A.heisenbergOne neg zer neg) = refl
nativeToWeil_compose (A.heisenbergOne zer pos zer) (A.heisenbergOne neg zer zer) = refl
nativeToWeil_compose (A.heisenbergOne zer pos zer) (A.heisenbergOne neg zer pos) = refl
nativeToWeil_compose (A.heisenbergOne zer pos zer) (A.heisenbergOne neg pos neg) = refl
nativeToWeil_compose (A.heisenbergOne zer pos zer) (A.heisenbergOne neg pos zer) = refl
nativeToWeil_compose (A.heisenbergOne zer pos zer) (A.heisenbergOne neg pos pos) = refl
nativeToWeil_compose (A.heisenbergOne zer pos zer) (A.heisenbergOne zer neg neg) = refl
nativeToWeil_compose (A.heisenbergOne zer pos zer) (A.heisenbergOne zer neg zer) = refl
nativeToWeil_compose (A.heisenbergOne zer pos zer) (A.heisenbergOne zer neg pos) = refl
nativeToWeil_compose (A.heisenbergOne zer pos zer) (A.heisenbergOne zer zer neg) = refl
nativeToWeil_compose (A.heisenbergOne zer pos zer) (A.heisenbergOne zer zer zer) = refl
nativeToWeil_compose (A.heisenbergOne zer pos zer) (A.heisenbergOne zer zer pos) = refl
nativeToWeil_compose (A.heisenbergOne zer pos zer) (A.heisenbergOne zer pos neg) = refl
nativeToWeil_compose (A.heisenbergOne zer pos zer) (A.heisenbergOne zer pos zer) = refl
nativeToWeil_compose (A.heisenbergOne zer pos zer) (A.heisenbergOne zer pos pos) = refl
nativeToWeil_compose (A.heisenbergOne zer pos zer) (A.heisenbergOne pos neg neg) = refl
nativeToWeil_compose (A.heisenbergOne zer pos zer) (A.heisenbergOne pos neg zer) = refl
nativeToWeil_compose (A.heisenbergOne zer pos zer) (A.heisenbergOne pos neg pos) = refl
nativeToWeil_compose (A.heisenbergOne zer pos zer) (A.heisenbergOne pos zer neg) = refl
nativeToWeil_compose (A.heisenbergOne zer pos zer) (A.heisenbergOne pos zer zer) = refl
nativeToWeil_compose (A.heisenbergOne zer pos zer) (A.heisenbergOne pos zer pos) = refl
nativeToWeil_compose (A.heisenbergOne zer pos zer) (A.heisenbergOne pos pos neg) = refl
nativeToWeil_compose (A.heisenbergOne zer pos zer) (A.heisenbergOne pos pos zer) = refl
nativeToWeil_compose (A.heisenbergOne zer pos zer) (A.heisenbergOne pos pos pos) = refl
nativeToWeil_compose (A.heisenbergOne zer pos pos) (A.heisenbergOne neg neg neg) = refl
nativeToWeil_compose (A.heisenbergOne zer pos pos) (A.heisenbergOne neg neg zer) = refl
nativeToWeil_compose (A.heisenbergOne zer pos pos) (A.heisenbergOne neg neg pos) = refl
nativeToWeil_compose (A.heisenbergOne zer pos pos) (A.heisenbergOne neg zer neg) = refl
nativeToWeil_compose (A.heisenbergOne zer pos pos) (A.heisenbergOne neg zer zer) = refl
nativeToWeil_compose (A.heisenbergOne zer pos pos) (A.heisenbergOne neg zer pos) = refl
nativeToWeil_compose (A.heisenbergOne zer pos pos) (A.heisenbergOne neg pos neg) = refl
nativeToWeil_compose (A.heisenbergOne zer pos pos) (A.heisenbergOne neg pos zer) = refl
nativeToWeil_compose (A.heisenbergOne zer pos pos) (A.heisenbergOne neg pos pos) = refl
nativeToWeil_compose (A.heisenbergOne zer pos pos) (A.heisenbergOne zer neg neg) = refl
nativeToWeil_compose (A.heisenbergOne zer pos pos) (A.heisenbergOne zer neg zer) = refl
nativeToWeil_compose (A.heisenbergOne zer pos pos) (A.heisenbergOne zer neg pos) = refl
nativeToWeil_compose (A.heisenbergOne zer pos pos) (A.heisenbergOne zer zer neg) = refl
nativeToWeil_compose (A.heisenbergOne zer pos pos) (A.heisenbergOne zer zer zer) = refl
nativeToWeil_compose (A.heisenbergOne zer pos pos) (A.heisenbergOne zer zer pos) = refl
nativeToWeil_compose (A.heisenbergOne zer pos pos) (A.heisenbergOne zer pos neg) = refl
nativeToWeil_compose (A.heisenbergOne zer pos pos) (A.heisenbergOne zer pos zer) = refl
nativeToWeil_compose (A.heisenbergOne zer pos pos) (A.heisenbergOne zer pos pos) = refl
nativeToWeil_compose (A.heisenbergOne zer pos pos) (A.heisenbergOne pos neg neg) = refl
nativeToWeil_compose (A.heisenbergOne zer pos pos) (A.heisenbergOne pos neg zer) = refl
nativeToWeil_compose (A.heisenbergOne zer pos pos) (A.heisenbergOne pos neg pos) = refl
nativeToWeil_compose (A.heisenbergOne zer pos pos) (A.heisenbergOne pos zer neg) = refl
nativeToWeil_compose (A.heisenbergOne zer pos pos) (A.heisenbergOne pos zer zer) = refl
nativeToWeil_compose (A.heisenbergOne zer pos pos) (A.heisenbergOne pos zer pos) = refl
nativeToWeil_compose (A.heisenbergOne zer pos pos) (A.heisenbergOne pos pos neg) = refl
nativeToWeil_compose (A.heisenbergOne zer pos pos) (A.heisenbergOne pos pos zer) = refl
nativeToWeil_compose (A.heisenbergOne zer pos pos) (A.heisenbergOne pos pos pos) = refl
nativeToWeil_compose (A.heisenbergOne pos neg neg) (A.heisenbergOne neg neg neg) = refl
nativeToWeil_compose (A.heisenbergOne pos neg neg) (A.heisenbergOne neg neg zer) = refl
nativeToWeil_compose (A.heisenbergOne pos neg neg) (A.heisenbergOne neg neg pos) = refl
nativeToWeil_compose (A.heisenbergOne pos neg neg) (A.heisenbergOne neg zer neg) = refl
nativeToWeil_compose (A.heisenbergOne pos neg neg) (A.heisenbergOne neg zer zer) = refl
nativeToWeil_compose (A.heisenbergOne pos neg neg) (A.heisenbergOne neg zer pos) = refl
nativeToWeil_compose (A.heisenbergOne pos neg neg) (A.heisenbergOne neg pos neg) = refl
nativeToWeil_compose (A.heisenbergOne pos neg neg) (A.heisenbergOne neg pos zer) = refl
nativeToWeil_compose (A.heisenbergOne pos neg neg) (A.heisenbergOne neg pos pos) = refl
nativeToWeil_compose (A.heisenbergOne pos neg neg) (A.heisenbergOne zer neg neg) = refl
nativeToWeil_compose (A.heisenbergOne pos neg neg) (A.heisenbergOne zer neg zer) = refl
nativeToWeil_compose (A.heisenbergOne pos neg neg) (A.heisenbergOne zer neg pos) = refl
nativeToWeil_compose (A.heisenbergOne pos neg neg) (A.heisenbergOne zer zer neg) = refl
nativeToWeil_compose (A.heisenbergOne pos neg neg) (A.heisenbergOne zer zer zer) = refl
nativeToWeil_compose (A.heisenbergOne pos neg neg) (A.heisenbergOne zer zer pos) = refl
nativeToWeil_compose (A.heisenbergOne pos neg neg) (A.heisenbergOne zer pos neg) = refl
nativeToWeil_compose (A.heisenbergOne pos neg neg) (A.heisenbergOne zer pos zer) = refl
nativeToWeil_compose (A.heisenbergOne pos neg neg) (A.heisenbergOne zer pos pos) = refl
nativeToWeil_compose (A.heisenbergOne pos neg neg) (A.heisenbergOne pos neg neg) = refl
nativeToWeil_compose (A.heisenbergOne pos neg neg) (A.heisenbergOne pos neg zer) = refl
nativeToWeil_compose (A.heisenbergOne pos neg neg) (A.heisenbergOne pos neg pos) = refl
nativeToWeil_compose (A.heisenbergOne pos neg neg) (A.heisenbergOne pos zer neg) = refl
nativeToWeil_compose (A.heisenbergOne pos neg neg) (A.heisenbergOne pos zer zer) = refl
nativeToWeil_compose (A.heisenbergOne pos neg neg) (A.heisenbergOne pos zer pos) = refl
nativeToWeil_compose (A.heisenbergOne pos neg neg) (A.heisenbergOne pos pos neg) = refl
nativeToWeil_compose (A.heisenbergOne pos neg neg) (A.heisenbergOne pos pos zer) = refl
nativeToWeil_compose (A.heisenbergOne pos neg neg) (A.heisenbergOne pos pos pos) = refl
nativeToWeil_compose (A.heisenbergOne pos neg zer) (A.heisenbergOne neg neg neg) = refl
nativeToWeil_compose (A.heisenbergOne pos neg zer) (A.heisenbergOne neg neg zer) = refl
nativeToWeil_compose (A.heisenbergOne pos neg zer) (A.heisenbergOne neg neg pos) = refl
nativeToWeil_compose (A.heisenbergOne pos neg zer) (A.heisenbergOne neg zer neg) = refl
nativeToWeil_compose (A.heisenbergOne pos neg zer) (A.heisenbergOne neg zer zer) = refl
nativeToWeil_compose (A.heisenbergOne pos neg zer) (A.heisenbergOne neg zer pos) = refl
nativeToWeil_compose (A.heisenbergOne pos neg zer) (A.heisenbergOne neg pos neg) = refl
nativeToWeil_compose (A.heisenbergOne pos neg zer) (A.heisenbergOne neg pos zer) = refl
nativeToWeil_compose (A.heisenbergOne pos neg zer) (A.heisenbergOne neg pos pos) = refl
nativeToWeil_compose (A.heisenbergOne pos neg zer) (A.heisenbergOne zer neg neg) = refl
nativeToWeil_compose (A.heisenbergOne pos neg zer) (A.heisenbergOne zer neg zer) = refl
nativeToWeil_compose (A.heisenbergOne pos neg zer) (A.heisenbergOne zer neg pos) = refl
nativeToWeil_compose (A.heisenbergOne pos neg zer) (A.heisenbergOne zer zer neg) = refl
nativeToWeil_compose (A.heisenbergOne pos neg zer) (A.heisenbergOne zer zer zer) = refl
nativeToWeil_compose (A.heisenbergOne pos neg zer) (A.heisenbergOne zer zer pos) = refl
nativeToWeil_compose (A.heisenbergOne pos neg zer) (A.heisenbergOne zer pos neg) = refl
nativeToWeil_compose (A.heisenbergOne pos neg zer) (A.heisenbergOne zer pos zer) = refl
nativeToWeil_compose (A.heisenbergOne pos neg zer) (A.heisenbergOne zer pos pos) = refl
nativeToWeil_compose (A.heisenbergOne pos neg zer) (A.heisenbergOne pos neg neg) = refl
nativeToWeil_compose (A.heisenbergOne pos neg zer) (A.heisenbergOne pos neg zer) = refl
nativeToWeil_compose (A.heisenbergOne pos neg zer) (A.heisenbergOne pos neg pos) = refl
nativeToWeil_compose (A.heisenbergOne pos neg zer) (A.heisenbergOne pos zer neg) = refl
nativeToWeil_compose (A.heisenbergOne pos neg zer) (A.heisenbergOne pos zer zer) = refl
nativeToWeil_compose (A.heisenbergOne pos neg zer) (A.heisenbergOne pos zer pos) = refl
nativeToWeil_compose (A.heisenbergOne pos neg zer) (A.heisenbergOne pos pos neg) = refl
nativeToWeil_compose (A.heisenbergOne pos neg zer) (A.heisenbergOne pos pos zer) = refl
nativeToWeil_compose (A.heisenbergOne pos neg zer) (A.heisenbergOne pos pos pos) = refl
nativeToWeil_compose (A.heisenbergOne pos neg pos) (A.heisenbergOne neg neg neg) = refl
nativeToWeil_compose (A.heisenbergOne pos neg pos) (A.heisenbergOne neg neg zer) = refl
nativeToWeil_compose (A.heisenbergOne pos neg pos) (A.heisenbergOne neg neg pos) = refl
nativeToWeil_compose (A.heisenbergOne pos neg pos) (A.heisenbergOne neg zer neg) = refl
nativeToWeil_compose (A.heisenbergOne pos neg pos) (A.heisenbergOne neg zer zer) = refl
nativeToWeil_compose (A.heisenbergOne pos neg pos) (A.heisenbergOne neg zer pos) = refl
nativeToWeil_compose (A.heisenbergOne pos neg pos) (A.heisenbergOne neg pos neg) = refl
nativeToWeil_compose (A.heisenbergOne pos neg pos) (A.heisenbergOne neg pos zer) = refl
nativeToWeil_compose (A.heisenbergOne pos neg pos) (A.heisenbergOne neg pos pos) = refl
nativeToWeil_compose (A.heisenbergOne pos neg pos) (A.heisenbergOne zer neg neg) = refl
nativeToWeil_compose (A.heisenbergOne pos neg pos) (A.heisenbergOne zer neg zer) = refl
nativeToWeil_compose (A.heisenbergOne pos neg pos) (A.heisenbergOne zer neg pos) = refl
nativeToWeil_compose (A.heisenbergOne pos neg pos) (A.heisenbergOne zer zer neg) = refl
nativeToWeil_compose (A.heisenbergOne pos neg pos) (A.heisenbergOne zer zer zer) = refl
nativeToWeil_compose (A.heisenbergOne pos neg pos) (A.heisenbergOne zer zer pos) = refl
nativeToWeil_compose (A.heisenbergOne pos neg pos) (A.heisenbergOne zer pos neg) = refl
nativeToWeil_compose (A.heisenbergOne pos neg pos) (A.heisenbergOne zer pos zer) = refl
nativeToWeil_compose (A.heisenbergOne pos neg pos) (A.heisenbergOne zer pos pos) = refl
nativeToWeil_compose (A.heisenbergOne pos neg pos) (A.heisenbergOne pos neg neg) = refl
nativeToWeil_compose (A.heisenbergOne pos neg pos) (A.heisenbergOne pos neg zer) = refl
nativeToWeil_compose (A.heisenbergOne pos neg pos) (A.heisenbergOne pos neg pos) = refl
nativeToWeil_compose (A.heisenbergOne pos neg pos) (A.heisenbergOne pos zer neg) = refl
nativeToWeil_compose (A.heisenbergOne pos neg pos) (A.heisenbergOne pos zer zer) = refl
nativeToWeil_compose (A.heisenbergOne pos neg pos) (A.heisenbergOne pos zer pos) = refl
nativeToWeil_compose (A.heisenbergOne pos neg pos) (A.heisenbergOne pos pos neg) = refl
nativeToWeil_compose (A.heisenbergOne pos neg pos) (A.heisenbergOne pos pos zer) = refl
nativeToWeil_compose (A.heisenbergOne pos neg pos) (A.heisenbergOne pos pos pos) = refl
nativeToWeil_compose (A.heisenbergOne pos zer neg) (A.heisenbergOne neg neg neg) = refl
nativeToWeil_compose (A.heisenbergOne pos zer neg) (A.heisenbergOne neg neg zer) = refl
nativeToWeil_compose (A.heisenbergOne pos zer neg) (A.heisenbergOne neg neg pos) = refl
nativeToWeil_compose (A.heisenbergOne pos zer neg) (A.heisenbergOne neg zer neg) = refl
nativeToWeil_compose (A.heisenbergOne pos zer neg) (A.heisenbergOne neg zer zer) = refl
nativeToWeil_compose (A.heisenbergOne pos zer neg) (A.heisenbergOne neg zer pos) = refl
nativeToWeil_compose (A.heisenbergOne pos zer neg) (A.heisenbergOne neg pos neg) = refl
nativeToWeil_compose (A.heisenbergOne pos zer neg) (A.heisenbergOne neg pos zer) = refl
nativeToWeil_compose (A.heisenbergOne pos zer neg) (A.heisenbergOne neg pos pos) = refl
nativeToWeil_compose (A.heisenbergOne pos zer neg) (A.heisenbergOne zer neg neg) = refl
nativeToWeil_compose (A.heisenbergOne pos zer neg) (A.heisenbergOne zer neg zer) = refl
nativeToWeil_compose (A.heisenbergOne pos zer neg) (A.heisenbergOne zer neg pos) = refl
nativeToWeil_compose (A.heisenbergOne pos zer neg) (A.heisenbergOne zer zer neg) = refl
nativeToWeil_compose (A.heisenbergOne pos zer neg) (A.heisenbergOne zer zer zer) = refl
nativeToWeil_compose (A.heisenbergOne pos zer neg) (A.heisenbergOne zer zer pos) = refl
nativeToWeil_compose (A.heisenbergOne pos zer neg) (A.heisenbergOne zer pos neg) = refl
nativeToWeil_compose (A.heisenbergOne pos zer neg) (A.heisenbergOne zer pos zer) = refl
nativeToWeil_compose (A.heisenbergOne pos zer neg) (A.heisenbergOne zer pos pos) = refl
nativeToWeil_compose (A.heisenbergOne pos zer neg) (A.heisenbergOne pos neg neg) = refl
nativeToWeil_compose (A.heisenbergOne pos zer neg) (A.heisenbergOne pos neg zer) = refl
nativeToWeil_compose (A.heisenbergOne pos zer neg) (A.heisenbergOne pos neg pos) = refl
nativeToWeil_compose (A.heisenbergOne pos zer neg) (A.heisenbergOne pos zer neg) = refl
nativeToWeil_compose (A.heisenbergOne pos zer neg) (A.heisenbergOne pos zer zer) = refl
nativeToWeil_compose (A.heisenbergOne pos zer neg) (A.heisenbergOne pos zer pos) = refl
nativeToWeil_compose (A.heisenbergOne pos zer neg) (A.heisenbergOne pos pos neg) = refl
nativeToWeil_compose (A.heisenbergOne pos zer neg) (A.heisenbergOne pos pos zer) = refl
nativeToWeil_compose (A.heisenbergOne pos zer neg) (A.heisenbergOne pos pos pos) = refl
nativeToWeil_compose (A.heisenbergOne pos zer zer) (A.heisenbergOne neg neg neg) = refl
nativeToWeil_compose (A.heisenbergOne pos zer zer) (A.heisenbergOne neg neg zer) = refl
nativeToWeil_compose (A.heisenbergOne pos zer zer) (A.heisenbergOne neg neg pos) = refl
nativeToWeil_compose (A.heisenbergOne pos zer zer) (A.heisenbergOne neg zer neg) = refl
nativeToWeil_compose (A.heisenbergOne pos zer zer) (A.heisenbergOne neg zer zer) = refl
nativeToWeil_compose (A.heisenbergOne pos zer zer) (A.heisenbergOne neg zer pos) = refl
nativeToWeil_compose (A.heisenbergOne pos zer zer) (A.heisenbergOne neg pos neg) = refl
nativeToWeil_compose (A.heisenbergOne pos zer zer) (A.heisenbergOne neg pos zer) = refl
nativeToWeil_compose (A.heisenbergOne pos zer zer) (A.heisenbergOne neg pos pos) = refl
nativeToWeil_compose (A.heisenbergOne pos zer zer) (A.heisenbergOne zer neg neg) = refl
nativeToWeil_compose (A.heisenbergOne pos zer zer) (A.heisenbergOne zer neg zer) = refl
nativeToWeil_compose (A.heisenbergOne pos zer zer) (A.heisenbergOne zer neg pos) = refl
nativeToWeil_compose (A.heisenbergOne pos zer zer) (A.heisenbergOne zer zer neg) = refl
nativeToWeil_compose (A.heisenbergOne pos zer zer) (A.heisenbergOne zer zer zer) = refl
nativeToWeil_compose (A.heisenbergOne pos zer zer) (A.heisenbergOne zer zer pos) = refl
nativeToWeil_compose (A.heisenbergOne pos zer zer) (A.heisenbergOne zer pos neg) = refl
nativeToWeil_compose (A.heisenbergOne pos zer zer) (A.heisenbergOne zer pos zer) = refl
nativeToWeil_compose (A.heisenbergOne pos zer zer) (A.heisenbergOne zer pos pos) = refl
nativeToWeil_compose (A.heisenbergOne pos zer zer) (A.heisenbergOne pos neg neg) = refl
nativeToWeil_compose (A.heisenbergOne pos zer zer) (A.heisenbergOne pos neg zer) = refl
nativeToWeil_compose (A.heisenbergOne pos zer zer) (A.heisenbergOne pos neg pos) = refl
nativeToWeil_compose (A.heisenbergOne pos zer zer) (A.heisenbergOne pos zer neg) = refl
nativeToWeil_compose (A.heisenbergOne pos zer zer) (A.heisenbergOne pos zer zer) = refl
nativeToWeil_compose (A.heisenbergOne pos zer zer) (A.heisenbergOne pos zer pos) = refl
nativeToWeil_compose (A.heisenbergOne pos zer zer) (A.heisenbergOne pos pos neg) = refl
nativeToWeil_compose (A.heisenbergOne pos zer zer) (A.heisenbergOne pos pos zer) = refl
nativeToWeil_compose (A.heisenbergOne pos zer zer) (A.heisenbergOne pos pos pos) = refl
nativeToWeil_compose (A.heisenbergOne pos zer pos) (A.heisenbergOne neg neg neg) = refl
nativeToWeil_compose (A.heisenbergOne pos zer pos) (A.heisenbergOne neg neg zer) = refl
nativeToWeil_compose (A.heisenbergOne pos zer pos) (A.heisenbergOne neg neg pos) = refl
nativeToWeil_compose (A.heisenbergOne pos zer pos) (A.heisenbergOne neg zer neg) = refl
nativeToWeil_compose (A.heisenbergOne pos zer pos) (A.heisenbergOne neg zer zer) = refl
nativeToWeil_compose (A.heisenbergOne pos zer pos) (A.heisenbergOne neg zer pos) = refl
nativeToWeil_compose (A.heisenbergOne pos zer pos) (A.heisenbergOne neg pos neg) = refl
nativeToWeil_compose (A.heisenbergOne pos zer pos) (A.heisenbergOne neg pos zer) = refl
nativeToWeil_compose (A.heisenbergOne pos zer pos) (A.heisenbergOne neg pos pos) = refl
nativeToWeil_compose (A.heisenbergOne pos zer pos) (A.heisenbergOne zer neg neg) = refl
nativeToWeil_compose (A.heisenbergOne pos zer pos) (A.heisenbergOne zer neg zer) = refl
nativeToWeil_compose (A.heisenbergOne pos zer pos) (A.heisenbergOne zer neg pos) = refl
nativeToWeil_compose (A.heisenbergOne pos zer pos) (A.heisenbergOne zer zer neg) = refl
nativeToWeil_compose (A.heisenbergOne pos zer pos) (A.heisenbergOne zer zer zer) = refl
nativeToWeil_compose (A.heisenbergOne pos zer pos) (A.heisenbergOne zer zer pos) = refl
nativeToWeil_compose (A.heisenbergOne pos zer pos) (A.heisenbergOne zer pos neg) = refl
nativeToWeil_compose (A.heisenbergOne pos zer pos) (A.heisenbergOne zer pos zer) = refl
nativeToWeil_compose (A.heisenbergOne pos zer pos) (A.heisenbergOne zer pos pos) = refl
nativeToWeil_compose (A.heisenbergOne pos zer pos) (A.heisenbergOne pos neg neg) = refl
nativeToWeil_compose (A.heisenbergOne pos zer pos) (A.heisenbergOne pos neg zer) = refl
nativeToWeil_compose (A.heisenbergOne pos zer pos) (A.heisenbergOne pos neg pos) = refl
nativeToWeil_compose (A.heisenbergOne pos zer pos) (A.heisenbergOne pos zer neg) = refl
nativeToWeil_compose (A.heisenbergOne pos zer pos) (A.heisenbergOne pos zer zer) = refl
nativeToWeil_compose (A.heisenbergOne pos zer pos) (A.heisenbergOne pos zer pos) = refl
nativeToWeil_compose (A.heisenbergOne pos zer pos) (A.heisenbergOne pos pos neg) = refl
nativeToWeil_compose (A.heisenbergOne pos zer pos) (A.heisenbergOne pos pos zer) = refl
nativeToWeil_compose (A.heisenbergOne pos zer pos) (A.heisenbergOne pos pos pos) = refl
nativeToWeil_compose (A.heisenbergOne pos pos neg) (A.heisenbergOne neg neg neg) = refl
nativeToWeil_compose (A.heisenbergOne pos pos neg) (A.heisenbergOne neg neg zer) = refl
nativeToWeil_compose (A.heisenbergOne pos pos neg) (A.heisenbergOne neg neg pos) = refl
nativeToWeil_compose (A.heisenbergOne pos pos neg) (A.heisenbergOne neg zer neg) = refl
nativeToWeil_compose (A.heisenbergOne pos pos neg) (A.heisenbergOne neg zer zer) = refl
nativeToWeil_compose (A.heisenbergOne pos pos neg) (A.heisenbergOne neg zer pos) = refl
nativeToWeil_compose (A.heisenbergOne pos pos neg) (A.heisenbergOne neg pos neg) = refl
nativeToWeil_compose (A.heisenbergOne pos pos neg) (A.heisenbergOne neg pos zer) = refl
nativeToWeil_compose (A.heisenbergOne pos pos neg) (A.heisenbergOne neg pos pos) = refl
nativeToWeil_compose (A.heisenbergOne pos pos neg) (A.heisenbergOne zer neg neg) = refl
nativeToWeil_compose (A.heisenbergOne pos pos neg) (A.heisenbergOne zer neg zer) = refl
nativeToWeil_compose (A.heisenbergOne pos pos neg) (A.heisenbergOne zer neg pos) = refl
nativeToWeil_compose (A.heisenbergOne pos pos neg) (A.heisenbergOne zer zer neg) = refl
nativeToWeil_compose (A.heisenbergOne pos pos neg) (A.heisenbergOne zer zer zer) = refl
nativeToWeil_compose (A.heisenbergOne pos pos neg) (A.heisenbergOne zer zer pos) = refl
nativeToWeil_compose (A.heisenbergOne pos pos neg) (A.heisenbergOne zer pos neg) = refl
nativeToWeil_compose (A.heisenbergOne pos pos neg) (A.heisenbergOne zer pos zer) = refl
nativeToWeil_compose (A.heisenbergOne pos pos neg) (A.heisenbergOne zer pos pos) = refl
nativeToWeil_compose (A.heisenbergOne pos pos neg) (A.heisenbergOne pos neg neg) = refl
nativeToWeil_compose (A.heisenbergOne pos pos neg) (A.heisenbergOne pos neg zer) = refl
nativeToWeil_compose (A.heisenbergOne pos pos neg) (A.heisenbergOne pos neg pos) = refl
nativeToWeil_compose (A.heisenbergOne pos pos neg) (A.heisenbergOne pos zer neg) = refl
nativeToWeil_compose (A.heisenbergOne pos pos neg) (A.heisenbergOne pos zer zer) = refl
nativeToWeil_compose (A.heisenbergOne pos pos neg) (A.heisenbergOne pos zer pos) = refl
nativeToWeil_compose (A.heisenbergOne pos pos neg) (A.heisenbergOne pos pos neg) = refl
nativeToWeil_compose (A.heisenbergOne pos pos neg) (A.heisenbergOne pos pos zer) = refl
nativeToWeil_compose (A.heisenbergOne pos pos neg) (A.heisenbergOne pos pos pos) = refl
nativeToWeil_compose (A.heisenbergOne pos pos zer) (A.heisenbergOne neg neg neg) = refl
nativeToWeil_compose (A.heisenbergOne pos pos zer) (A.heisenbergOne neg neg zer) = refl
nativeToWeil_compose (A.heisenbergOne pos pos zer) (A.heisenbergOne neg neg pos) = refl
nativeToWeil_compose (A.heisenbergOne pos pos zer) (A.heisenbergOne neg zer neg) = refl
nativeToWeil_compose (A.heisenbergOne pos pos zer) (A.heisenbergOne neg zer zer) = refl
nativeToWeil_compose (A.heisenbergOne pos pos zer) (A.heisenbergOne neg zer pos) = refl
nativeToWeil_compose (A.heisenbergOne pos pos zer) (A.heisenbergOne neg pos neg) = refl
nativeToWeil_compose (A.heisenbergOne pos pos zer) (A.heisenbergOne neg pos zer) = refl
nativeToWeil_compose (A.heisenbergOne pos pos zer) (A.heisenbergOne neg pos pos) = refl
nativeToWeil_compose (A.heisenbergOne pos pos zer) (A.heisenbergOne zer neg neg) = refl
nativeToWeil_compose (A.heisenbergOne pos pos zer) (A.heisenbergOne zer neg zer) = refl
nativeToWeil_compose (A.heisenbergOne pos pos zer) (A.heisenbergOne zer neg pos) = refl
nativeToWeil_compose (A.heisenbergOne pos pos zer) (A.heisenbergOne zer zer neg) = refl
nativeToWeil_compose (A.heisenbergOne pos pos zer) (A.heisenbergOne zer zer zer) = refl
nativeToWeil_compose (A.heisenbergOne pos pos zer) (A.heisenbergOne zer zer pos) = refl
nativeToWeil_compose (A.heisenbergOne pos pos zer) (A.heisenbergOne zer pos neg) = refl
nativeToWeil_compose (A.heisenbergOne pos pos zer) (A.heisenbergOne zer pos zer) = refl
nativeToWeil_compose (A.heisenbergOne pos pos zer) (A.heisenbergOne zer pos pos) = refl
nativeToWeil_compose (A.heisenbergOne pos pos zer) (A.heisenbergOne pos neg neg) = refl
nativeToWeil_compose (A.heisenbergOne pos pos zer) (A.heisenbergOne pos neg zer) = refl
nativeToWeil_compose (A.heisenbergOne pos pos zer) (A.heisenbergOne pos neg pos) = refl
nativeToWeil_compose (A.heisenbergOne pos pos zer) (A.heisenbergOne pos zer neg) = refl
nativeToWeil_compose (A.heisenbergOne pos pos zer) (A.heisenbergOne pos zer zer) = refl
nativeToWeil_compose (A.heisenbergOne pos pos zer) (A.heisenbergOne pos zer pos) = refl
nativeToWeil_compose (A.heisenbergOne pos pos zer) (A.heisenbergOne pos pos neg) = refl
nativeToWeil_compose (A.heisenbergOne pos pos zer) (A.heisenbergOne pos pos zer) = refl
nativeToWeil_compose (A.heisenbergOne pos pos zer) (A.heisenbergOne pos pos pos) = refl
nativeToWeil_compose (A.heisenbergOne pos pos pos) (A.heisenbergOne neg neg neg) = refl
nativeToWeil_compose (A.heisenbergOne pos pos pos) (A.heisenbergOne neg neg zer) = refl
nativeToWeil_compose (A.heisenbergOne pos pos pos) (A.heisenbergOne neg neg pos) = refl
nativeToWeil_compose (A.heisenbergOne pos pos pos) (A.heisenbergOne neg zer neg) = refl
nativeToWeil_compose (A.heisenbergOne pos pos pos) (A.heisenbergOne neg zer zer) = refl
nativeToWeil_compose (A.heisenbergOne pos pos pos) (A.heisenbergOne neg zer pos) = refl
nativeToWeil_compose (A.heisenbergOne pos pos pos) (A.heisenbergOne neg pos neg) = refl
nativeToWeil_compose (A.heisenbergOne pos pos pos) (A.heisenbergOne neg pos zer) = refl
nativeToWeil_compose (A.heisenbergOne pos pos pos) (A.heisenbergOne neg pos pos) = refl
nativeToWeil_compose (A.heisenbergOne pos pos pos) (A.heisenbergOne zer neg neg) = refl
nativeToWeil_compose (A.heisenbergOne pos pos pos) (A.heisenbergOne zer neg zer) = refl
nativeToWeil_compose (A.heisenbergOne pos pos pos) (A.heisenbergOne zer neg pos) = refl
nativeToWeil_compose (A.heisenbergOne pos pos pos) (A.heisenbergOne zer zer neg) = refl
nativeToWeil_compose (A.heisenbergOne pos pos pos) (A.heisenbergOne zer zer zer) = refl
nativeToWeil_compose (A.heisenbergOne pos pos pos) (A.heisenbergOne zer zer pos) = refl
nativeToWeil_compose (A.heisenbergOne pos pos pos) (A.heisenbergOne zer pos neg) = refl
nativeToWeil_compose (A.heisenbergOne pos pos pos) (A.heisenbergOne zer pos zer) = refl
nativeToWeil_compose (A.heisenbergOne pos pos pos) (A.heisenbergOne zer pos pos) = refl
nativeToWeil_compose (A.heisenbergOne pos pos pos) (A.heisenbergOne pos neg neg) = refl
nativeToWeil_compose (A.heisenbergOne pos pos pos) (A.heisenbergOne pos neg zer) = refl
nativeToWeil_compose (A.heisenbergOne pos pos pos) (A.heisenbergOne pos neg pos) = refl
nativeToWeil_compose (A.heisenbergOne pos pos pos) (A.heisenbergOne pos zer neg) = refl
nativeToWeil_compose (A.heisenbergOne pos pos pos) (A.heisenbergOne pos zer zer) = refl
nativeToWeil_compose (A.heisenbergOne pos pos pos) (A.heisenbergOne pos zer pos) = refl
nativeToWeil_compose (A.heisenbergOne pos pos pos) (A.heisenbergOne pos pos neg) = refl
nativeToWeil_compose (A.heisenbergOne pos pos pos) (A.heisenbergOne pos pos zer) = refl
nativeToWeil_compose (A.heisenbergOne pos pos pos) (A.heisenbergOne pos pos pos) = refl

-- Explicit action on the physical centre of the Monster3B axis embedding.
-- Because z_Weil=-z_native on x=y=0, the central sign is not optional.
nativeCenterToWeil :
  (z : Trit) →
  nativeToWeil (A.centerOne z) ≡ W.centre (W.neg (tritToF3 z))
nativeCenterToWeil neg = refl
nativeCenterToWeil zer = refl
nativeCenterToWeil pos = refl

------------------------------------------------------------------------
-- Action-level transport: the quadratic correction is NOT a new action.
-- It is the exact native-cocycle representative of W.shearLift.
------------------------------------------------------------------------

nativeShearOne : A.RankOneHeisenberg → A.RankOneHeisenberg
nativeShearOne (A.heisenbergOne x y z) =
  A.heisenbergOne
    (G._+3_ x y) y
    (G._+3_ z (H._*3_ neg (H._*3_ y y)))

nativeShearToWeil :
  (g : A.RankOneHeisenberg) →
  nativeToWeil (nativeShearOne g)
  ≡ W.shearLift (nativeToWeil g)
nativeShearToWeil (A.heisenbergOne neg neg neg) = refl
nativeShearToWeil (A.heisenbergOne neg neg zer) = refl
nativeShearToWeil (A.heisenbergOne neg neg pos) = refl
nativeShearToWeil (A.heisenbergOne neg zer neg) = refl
nativeShearToWeil (A.heisenbergOne neg zer zer) = refl
nativeShearToWeil (A.heisenbergOne neg zer pos) = refl
nativeShearToWeil (A.heisenbergOne neg pos neg) = refl
nativeShearToWeil (A.heisenbergOne neg pos zer) = refl
nativeShearToWeil (A.heisenbergOne neg pos pos) = refl
nativeShearToWeil (A.heisenbergOne zer neg neg) = refl
nativeShearToWeil (A.heisenbergOne zer neg zer) = refl
nativeShearToWeil (A.heisenbergOne zer neg pos) = refl
nativeShearToWeil (A.heisenbergOne zer zer neg) = refl
nativeShearToWeil (A.heisenbergOne zer zer zer) = refl
nativeShearToWeil (A.heisenbergOne zer zer pos) = refl
nativeShearToWeil (A.heisenbergOne zer pos neg) = refl
nativeShearToWeil (A.heisenbergOne zer pos zer) = refl
nativeShearToWeil (A.heisenbergOne zer pos pos) = refl
nativeShearToWeil (A.heisenbergOne pos neg neg) = refl
nativeShearToWeil (A.heisenbergOne pos neg zer) = refl
nativeShearToWeil (A.heisenbergOne pos neg pos) = refl
nativeShearToWeil (A.heisenbergOne pos zer neg) = refl
nativeShearToWeil (A.heisenbergOne pos zer zer) = refl
nativeShearToWeil (A.heisenbergOne pos zer pos) = refl
nativeShearToWeil (A.heisenbergOne pos pos neg) = refl
nativeShearToWeil (A.heisenbergOne pos pos zer) = refl
nativeShearToWeil (A.heisenbergOne pos pos pos) = refl

nativeReflectionToWeil :
  (g : A.RankOneHeisenberg) →
  nativeToWeil (A.reflectionOne g)
  ≡ W.reflectionLift (nativeToWeil g)
nativeReflectionToWeil (A.heisenbergOne neg neg neg) = refl
nativeReflectionToWeil (A.heisenbergOne neg neg zer) = refl
nativeReflectionToWeil (A.heisenbergOne neg neg pos) = refl
nativeReflectionToWeil (A.heisenbergOne neg zer neg) = refl
nativeReflectionToWeil (A.heisenbergOne neg zer zer) = refl
nativeReflectionToWeil (A.heisenbergOne neg zer pos) = refl
nativeReflectionToWeil (A.heisenbergOne neg pos neg) = refl
nativeReflectionToWeil (A.heisenbergOne neg pos zer) = refl
nativeReflectionToWeil (A.heisenbergOne neg pos pos) = refl
nativeReflectionToWeil (A.heisenbergOne zer neg neg) = refl
nativeReflectionToWeil (A.heisenbergOne zer neg zer) = refl
nativeReflectionToWeil (A.heisenbergOne zer neg pos) = refl
nativeReflectionToWeil (A.heisenbergOne zer zer neg) = refl
nativeReflectionToWeil (A.heisenbergOne zer zer zer) = refl
nativeReflectionToWeil (A.heisenbergOne zer zer pos) = refl
nativeReflectionToWeil (A.heisenbergOne zer pos neg) = refl
nativeReflectionToWeil (A.heisenbergOne zer pos zer) = refl
nativeReflectionToWeil (A.heisenbergOne zer pos pos) = refl
nativeReflectionToWeil (A.heisenbergOne pos neg neg) = refl
nativeReflectionToWeil (A.heisenbergOne pos neg zer) = refl
nativeReflectionToWeil (A.heisenbergOne pos neg pos) = refl
nativeReflectionToWeil (A.heisenbergOne pos zer neg) = refl
nativeReflectionToWeil (A.heisenbergOne pos zer zer) = refl
nativeReflectionToWeil (A.heisenbergOne pos zer pos) = refl
nativeReflectionToWeil (A.heisenbergOne pos pos neg) = refl
nativeReflectionToWeil (A.heisenbergOne pos pos zer) = refl
nativeReflectionToWeil (A.heisenbergOne pos pos pos) = refl

-- The exact dihedral relation, now in the existing rank-one subgroup.
nativeDihedralRelation :
  (g : A.RankOneHeisenberg) →
  A.reflectionOne (nativeShearOne (A.reflectionOne g))
    ≡ nativeShearOne (nativeShearOne g)
nativeDihedralRelation (A.heisenbergOne neg neg neg) = refl
nativeDihedralRelation (A.heisenbergOne neg neg zer) = refl
nativeDihedralRelation (A.heisenbergOne neg neg pos) = refl
nativeDihedralRelation (A.heisenbergOne neg zer neg) = refl
nativeDihedralRelation (A.heisenbergOne neg zer zer) = refl
nativeDihedralRelation (A.heisenbergOne neg zer pos) = refl
nativeDihedralRelation (A.heisenbergOne neg pos neg) = refl
nativeDihedralRelation (A.heisenbergOne neg pos zer) = refl
nativeDihedralRelation (A.heisenbergOne neg pos pos) = refl
nativeDihedralRelation (A.heisenbergOne zer neg neg) = refl
nativeDihedralRelation (A.heisenbergOne zer neg zer) = refl
nativeDihedralRelation (A.heisenbergOne zer neg pos) = refl
nativeDihedralRelation (A.heisenbergOne zer zer neg) = refl
nativeDihedralRelation (A.heisenbergOne zer zer zer) = refl
nativeDihedralRelation (A.heisenbergOne zer zer pos) = refl
nativeDihedralRelation (A.heisenbergOne zer pos neg) = refl
nativeDihedralRelation (A.heisenbergOne zer pos zer) = refl
nativeDihedralRelation (A.heisenbergOne zer pos pos) = refl
nativeDihedralRelation (A.heisenbergOne pos neg neg) = refl
nativeDihedralRelation (A.heisenbergOne pos neg zer) = refl
nativeDihedralRelation (A.heisenbergOne pos neg pos) = refl
nativeDihedralRelation (A.heisenbergOne pos zer neg) = refl
nativeDihedralRelation (A.heisenbergOne pos zer zer) = refl
nativeDihedralRelation (A.heisenbergOne pos zer pos) = refl
nativeDihedralRelation (A.heisenbergOne pos pos neg) = refl
nativeDihedralRelation (A.heisenbergOne pos pos zer) = refl
nativeDihedralRelation (A.heisenbergOne pos pos pos) = refl

------------------------------------------------------------------------
-- Transport an ACTUAL associative group law from H6 to Weil.H3.
-- This is an associativity theorem about W.hprod itself, not a receipt.
------------------------------------------------------------------------

weilComposeViaNative :
  (a b : W.H3) →
  W.hprod a b
  ≡ nativeToWeil (A.composeOne (weilToNative a) (weilToNative b))
weilComposeViaNative a b =
  trans
    (cong (λ u → W.hprod u b) (sym (weilToNative_roundtrip a)))
    (trans
      (cong (λ v → W.hprod (nativeToWeil (weilToNative a)) v)
        (sym (weilToNative_roundtrip b)))
      (sym (nativeToWeil_compose (weilToNative a) (weilToNative b))))

weilToNativeProduct :
  (a b : W.H3) →
  weilToNative (W.hprod a b)
    ≡ A.composeOne (weilToNative a) (weilToNative b)
weilToNativeProduct a b =
  trans
    (cong weilToNative (weilComposeViaNative a b))
    (nativeToWeil_roundtrip (A.composeOne (weilToNative a) (weilToNative b)))

weilH3Associative :
  (a b c : W.H3) →
  W.hprod (W.hprod a b) c ≡ W.hprod a (W.hprod b c)
weilH3Associative a b c =
  trans
    (sym (weilToNative_roundtrip (W.hprod (W.hprod a b) c)))
    (trans
      (cong nativeToWeil (weilToNativeProduct (W.hprod a b) c))
      (trans
        (cong nativeToWeil
          (cong (λ u → A.composeOne u (weilToNative c))
            (weilToNativeProduct a b)))
        (trans
          (cong nativeToWeil
            (A.composeOneAssociative
              (weilToNative a) (weilToNative b) (weilToNative c)))
          (trans
            (cong nativeToWeil
              (sym (cong (λ u → A.composeOne (weilToNative a) u)
                (weilToNativeProduct b c))))
            (trans
              (cong nativeToWeil
                (sym (weilToNativeProduct a (W.hprod b c))))
              (weilToNative_roundtrip (W.hprod a (W.hprod b c)))))))
