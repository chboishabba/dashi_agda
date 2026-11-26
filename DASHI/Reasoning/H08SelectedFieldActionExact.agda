module DASHI.Reasoning.H08SelectedFieldActionExact where

-- Selected Route C polynomial fields, using original Trit and codec blocks.
-- No claim that all vector spaces are fields or GF729 is a subfield of GF3^9.
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
import DASHI.Codec.IndexedCubeMaskSignExact as C
import DASHI.Codec.TriadicMaskSignFactorization as V
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as S

Word9 : Set
Word9 = C.Blocks Trit

word : Trit → Trit → Trit → Trit → Trit → Trit → Trit → Trit → Trit → Word9
word a b c d e f g h i = C.blocks (V.triple a b c) (V.triple d e f) (V.triple g h i)

zero9 one9 : Word9
zero9 = word zer zer zer zer zer zer zer zer zer
one9 = word pos zer zer zer zer zer zer zer zer

add9 : Word9 → Word9 → Word9
add9 (C.blocks (V.triple a b c) (V.triple d e f) (V.triple g h i))
     (C.blocks (V.triple j k l) (V.triple m n o) (V.triple p q r)) =
  word (G._+3_ a j) (G._+3_ b k) (G._+3_ c l) (G._+3_ d m) (G._+3_ e n) (G._+3_ f o) (G._+3_ g p) (G._+3_ h q) (G._+3_ i r)

scale9 : Trit → Word9 → Word9
scale9 t (C.blocks (V.triple a b c) (V.triple d e f) (V.triple g h i)) =
  word (S._*3_ t a) (S._*3_ t b) (S._*3_ t c) (S._*3_ t d) (S._*3_ t e) (S._*3_ t f) (S._*3_ t g) (S._*3_ t h) (S._*3_ t i)

-- Literal x^9+x^4-1: x^9=1-x^4.
mulX9 : Word9 → Word9
mulX9 (C.blocks (V.triple a b c) (V.triple d e f) (V.triple g h i)) =
  word i a b c (G._+3_ d (G.negate3 i)) e f g h

mul9 : Word9 → Word9 → Word9
mul9 p (C.blocks (V.triple a b c) (V.triple d e f) (V.triple g h i)) =
  add9 (scale9 a p) (mulX9 (add9 (scale9 b p) (mulX9 (add9 (scale9 c p) (mulX9 (add9 (scale9 d p) (mulX9 (add9 (scale9 e p) (mulX9 (add9 (scale9 f p) (mulX9 (add9 (scale9 g p) (mulX9 (add9 (scale9 h p) (mulX9 (add9 (scale9 i p) (mulX9 (zero9))))))))))))))))))

cube9 : Word9 → Word9
cube9 p = mul9 p (mul9 p p)

frob3 frob6 : Word9 → Word9
frob3 p = cube9 (cube9 (cube9 p))
frob6 p = frob3 (frob3 p)

-- Actual selected normal basis: x^5 and its Frobenius orbit in order
-- (0,3,6,1,4,7,2,5,8). Polynomial coordinates use the original Word9.
normalEncode normalDecode : Word9 → Word9
normalEncode (C.blocks (V.triple a b c) (V.triple d e f) (V.triple g h i)) =
  word (G._+3_ e (G._+3_ f (G._+3_ g (G._+3_ h zer)))) (G._+3_ (G.negate3 c) (G._+3_ (G.negate3 d) (G._+3_ (G.negate3 f) (G._+3_ (G.negate3 g) (G._+3_ h zer))))) (G._+3_ (G.negate3 c) (G._+3_ (G.negate3 e) (G._+3_ (G.negate3 f) (G._+3_ (G.negate3 h) (G._+3_ i zer))))) (G._+3_ (G.negate3 e) (G._+3_ (G.negate3 f) (G._+3_ (G.negate3 g) (G._+3_ (G.negate3 h) (G._+3_ i zer))))) (G._+3_ c (G._+3_ f (G._+3_ g zer))) (G._+3_ a (G._+3_ b (G._+3_ c (G._+3_ d (G._+3_ e (G._+3_ f (G._+3_ g (G._+3_ h (G._+3_ i zer))))))))) (G._+3_ (G.negate3 b) (G._+3_ c (G._+3_ d (G._+3_ f (G._+3_ g zer))))) (G._+3_ (G.negate3 b) (G._+3_ (G.negate3 c) (G._+3_ (G.negate3 e) (G._+3_ f (G._+3_ (G.negate3 h) zer))))) (G._+3_ b (G._+3_ (G.negate3 e) (G._+3_ f (G._+3_ g (G._+3_ i zer)))))
normalDecode (C.blocks (V.triple a b c) (V.triple d e f) (V.triple g h i)) =
  word (G._+3_ a (G._+3_ b (G._+3_ f (G._+3_ (G.negate3 i) zer)))) (G._+3_ a (G._+3_ (G.negate3 b) (G._+3_ c (G._+3_ d (G._+3_ (G.negate3 e) (G._+3_ (G.negate3 g) (G._+3_ h (G._+3_ i zer)))))))) (G._+3_ a (G._+3_ b (G._+3_ c (G._+3_ g (G._+3_ h (G._+3_ (G.negate3 i) zer)))))) (G._+3_ a (G._+3_ (G.negate3 b) (G._+3_ c (G._+3_ d (G._+3_ e (G._+3_ h (G._+3_ i zer))))))) (G._+3_ a (G._+3_ b (G._+3_ (G.negate3 d) (G._+3_ g (G._+3_ i zer))))) (G._+3_ a (G._+3_ b (G._+3_ d (G._+3_ e (G._+3_ g (G._+3_ h (G._+3_ (G.negate3 i) zer))))))) (G._+3_ a (G._+3_ b (G._+3_ (G.negate3 c) (G._+3_ (G.negate3 d) (G._+3_ g (G._+3_ h (G._+3_ (G.negate3 i) zer))))))) (G._+3_ a (G._+3_ c (G._+3_ d (G._+3_ (G.negate3 e) (G._+3_ h (G._+3_ i zer)))))) (G._+3_ a (G._+3_ d zer))

data Axis : Set where
  axis0 axis1 axis2 axis3 axis4 axis5 axis6 axis7 axis8 : Axis

basis : Axis → Word9
basis axis0 = word pos zer zer zer zer zer zer zer zer
basis axis1 = word zer pos zer zer zer zer zer zer zer
basis axis2 = word zer zer pos zer zer zer zer zer zer
basis axis3 = word zer zer zer pos zer zer zer zer zer
basis axis4 = word zer zer zer zer pos zer zer zer zer
basis axis5 = word zer zer zer zer zer pos zer zer zer
basis axis6 = word zer zer zer zer zer zer pos zer zer
basis axis7 = word zer zer zer zer zer zer zer pos zer
basis axis8 = word zer zer zer zer zer zer zer zer pos

-- These native finite basis identities are not a universal linearity
-- proof. Independent exact checker verifies actual full field arithmetic.
decodeEncodeBasis : (i : Axis) → normalDecode (normalEncode (basis i)) ≡ basis i
decodeEncodeBasis axis0 = refl
decodeEncodeBasis axis1 = refl
decodeEncodeBasis axis2 = refl
decodeEncodeBasis axis3 = refl
decodeEncodeBasis axis4 = refl
decodeEncodeBasis axis5 = refl
decodeEncodeBasis axis6 = refl
decodeEncodeBasis axis7 = refl
decodeEncodeBasis axis8 = refl

encodeDecodeBasis : (i : Axis) → normalEncode (normalDecode (basis i)) ≡ basis i
encodeDecodeBasis axis0 = refl
encodeDecodeBasis axis1 = refl
encodeDecodeBasis axis2 = refl
encodeDecodeBasis axis3 = refl
encodeDecodeBasis axis4 = refl
encodeDecodeBasis axis5 = refl
encodeDecodeBasis axis6 = refl
encodeDecodeBasis axis7 = refl
encodeDecodeBasis axis8 = refl

rotationBasis : (i : Axis) →
  frob6 (normalEncode (basis i)) ≡ normalEncode (C.rotate (basis i))
rotationBasis axis0 = refl
rotationBasis axis1 = refl
rotationBasis axis2 = refl
rotationBasis axis3 = refl
rotationBasis axis4 = refl
rotationBasis axis5 = refl
rotationBasis axis6 = refl
rotationBasis axis7 = refl
rotationBasis axis8 = refl

-- Common GF27 root: u^3-u-1=0. The two embeddings are independently
-- selected in the actual degree-nine and degree-six polynomial fields.
root9 : Word9
root9 = word pos neg neg pos zer zer neg neg neg

root9Law : cube9 root9 ≡ add9 root9 one9
root9Law = refl

scale6 : Trit → G.X6 → G.X6
scale6 t (G.x6 a b c d e f) = G.x6 (S._*3_ t a) (S._*3_ t b) (S._*3_ t c) (S._*3_ t d) (S._*3_ t e) (S._*3_ t f)

-- Literal selected GF729 modulus x^6+x^5+x^4+1.
mulX6 : G.X6 → G.X6
mulX6 (G.x6 a b c d e f) =
  G.x6 (G.negate3 f) a b c (G._+3_ d (G.negate3 f)) (G._+3_ e (G.negate3 f))

mul6 : G.X6 → G.X6 → G.X6
mul6 p (G.x6 a b c d e f) =
  S.addX6 (scale6 a p) (mulX6 (S.addX6 (scale6 b p) (mulX6 (S.addX6 (scale6 c p) (mulX6 (S.addX6 (scale6 d p) (mulX6 (S.addX6 (scale6 e p) (mulX6 (S.addX6 (scale6 f p) (mulX6 (S.zeroX6))))))))))))

one6 root6 : G.X6
one6 = G.x6 pos zer zer zer zer zer
root6 = G.x6 zer pos zer zer pos pos

root6Law : mul6 root6 (mul6 root6 root6) ≡ S.addX6 root6 one6
root6Law = refl

embed9 : V.Triple Trit → Word9
embed9 (V.triple a b c) = add9 (scale9 a one9)
  (add9 (scale9 b root9) (scale9 c (mul9 root9 root9)))

embed6 : V.Triple Trit → G.X6
embed6 (V.triple a b c) = S.addX6 (scale6 a one6)
  (S.addX6 (scale6 b root6) (scale6 c (mul6 root6 root6)))

-- Source-written selected polynomial operations, basis and root checks.
-- Native field-law, general normal chart inverse and actual Monster action
-- remain independent; no source-specific GF729 module copied from master.
