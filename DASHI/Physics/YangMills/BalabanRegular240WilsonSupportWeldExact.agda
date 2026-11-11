module DASHI.Physics.YangMills.BalabanRegular240WilsonSupportWeldExact where

-- Same-source identification of support masks in the new 240×F4
-- half-root geometry and the ORIGINAL BalabanWilsonBooleanFourCubeExact.
-- All sixteen support masks are identified constructively; the empty
-- support remains the 16-cell infrared fibre, and nonempty supports
-- are exactly the 15 original nonempty Boolean Wilson atoms.
--
-- No selected one-loop integrand invariance or exceptional E6/E8
-- representation is inferred from this discrete carrier weld.
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanRegular240SupportHalfExact as Product
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanClayT4HypercubicOrbitGeometryExact as Orbit
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid

toWilson : Product.Mask4 → Cube.Subset4
toWilson (Product.mask4 false false false false) = Cube.empty
toWilson (Product.mask4 true false false false) = Cube.s0
toWilson (Product.mask4 false true false false) = Cube.s1
toWilson (Product.mask4 false false true false) = Cube.s2
toWilson (Product.mask4 false false false true) = Cube.s3
toWilson (Product.mask4 true true false false) = Cube.s01
toWilson (Product.mask4 true false true false) = Cube.s02
toWilson (Product.mask4 true false false true) = Cube.s03
toWilson (Product.mask4 false true true false) = Cube.s12
toWilson (Product.mask4 false true false true) = Cube.s13
toWilson (Product.mask4 false false true true) = Cube.s23
toWilson (Product.mask4 true true true false) = Cube.s012
toWilson (Product.mask4 true true false true) = Cube.s013
toWilson (Product.mask4 true false true true) = Cube.s023
toWilson (Product.mask4 false true true true) = Cube.s123
toWilson (Product.mask4 true true true true) = Cube.s0123

fromWilson : Cube.Subset4 → Product.Mask4
fromWilson s =
  Product.mask4 (Cube.contains Cube.slot0 s)
                (Cube.contains Cube.slot1 s)
                (Cube.contains Cube.slot2 s)
                (Cube.contains Cube.slot3 s)

wilsonRoundTrip : (s : Cube.Subset4) → toWilson (fromWilson s) ≡ s
wilsonRoundTrip Cube.empty = refl
wilsonRoundTrip Cube.s0 = refl
wilsonRoundTrip Cube.s1 = refl
wilsonRoundTrip Cube.s2 = refl
wilsonRoundTrip Cube.s3 = refl
wilsonRoundTrip Cube.s01 = refl
wilsonRoundTrip Cube.s02 = refl
wilsonRoundTrip Cube.s03 = refl
wilsonRoundTrip Cube.s12 = refl
wilsonRoundTrip Cube.s13 = refl
wilsonRoundTrip Cube.s23 = refl
wilsonRoundTrip Cube.s012 = refl
wilsonRoundTrip Cube.s013 = refl
wilsonRoundTrip Cube.s023 = refl
wilsonRoundTrip Cube.s123 = refl
wilsonRoundTrip Cube.s0123 = refl

maskRoundTrip : (m : Product.Mask4) → fromWilson (toWilson m) ≡ m
maskRoundTrip (Product.mask4 false false false false) = refl
maskRoundTrip (Product.mask4 true false false false) = refl
maskRoundTrip (Product.mask4 false true false false) = refl
maskRoundTrip (Product.mask4 false false true false) = refl
maskRoundTrip (Product.mask4 false false false true) = refl
maskRoundTrip (Product.mask4 true true false false) = refl
maskRoundTrip (Product.mask4 true false true false) = refl
maskRoundTrip (Product.mask4 true false false true) = refl
maskRoundTrip (Product.mask4 false true true false) = refl
maskRoundTrip (Product.mask4 false true false true) = refl
maskRoundTrip (Product.mask4 false false true true) = refl
maskRoundTrip (Product.mask4 true true true false) = refl
maskRoundTrip (Product.mask4 true true false true) = refl
maskRoundTrip (Product.mask4 true false true true) = refl
maskRoundTrip (Product.mask4 false true true true) = refl
maskRoundTrip (Product.mask4 true true true true) = refl

-- Exact source alignment; not merely two carriers of cardinality 16.
-- Both source maps read the SAME original four interval cells.
sameOriginalWilsonSupport :
  (cell : Grid.GridCell4) →
  toWilson (Product.supportMask (Product.encode256 cell)) ≡
  Orbit.outerSubset cell
sameOriginalWilsonSupport (Grid.gridCell4 a b c d) with
  Orbit.outerFlag a |
  Orbit.outerFlag b |
  Orbit.outerFlag c |
  Orbit.outerFlag d
... | false | false | false | false = refl
... | true  | false | false | false = refl
... | false | true  | false | false = refl
... | false | false | true  | false = refl
... | false | false | false | true  = refl
... | true  | true  | false | false = refl
... | true  | false | true  | false = refl
... | true  | false | false | true  = refl
... | false | true  | true  | false = refl
... | false | true  | false | true  = refl
... | false | false | true  | true  = refl
... | true  | true  | true  | false = refl
... | true  | true  | false | true  = refl
... | true  | false | true  | true  = refl
... | false | true  | true  | true  = refl
... | true  | true  | true  | true  = refl

-- This aligns exactly with the Wilson four-cube's original 15 nonempty
-- atoms and the Round56 four-representative orbit decomposition.
