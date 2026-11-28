module DASHI.Moonshine.SignedNonaryPrime43S3GeometryExact where

-- Source-written, kernel pending. The original S3 law owner is reused.
-- The previous cyclic chart is retained; a sign-dependent base antipode
-- makes the nonabelian final-letter action the actual torus normalizer.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Fin using (Fin; toℕ)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
open import DASHI.Foundations.Base369Nat using (_%_)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos; inv)
open import DASHI.Codec.BalancedTritBitFibre using (Sign; positiveSign; negativeSign; invertSign)
import Base369 as Base
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as G
import DASHI.Foundations.TernaryPermutationS3LawsExact as Laws
open Laws using (_∙_)
import DASHI.Moonshine.SignedNonaryPrime43CodecExact as W
open W using (Hex; hex; Word42; one; two; Word43; empty; live; Seven; centre; active)
import DASHI.Moonshine.CM163Hecke41Signed43TorusExact as Torus
import DASHI.Moonshine.CM163BishopHecke41ProductExact as Prod
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C

-- Hex(t,s) is the affine permutation x -> a*x+b over F3:
-- t indexes b=0,1,2 and s indexes a=+1,-1.
asGroup : Hex → G.TriPermutation
asGroup (hex neg positiveSign) = G.permIdentity
asGroup (hex zer positiveSign) = G.permRotate
asGroup (hex pos positiveSign) = G.permRotate2
asGroup (hex neg negativeSign) = G.permSwapMidHigh
asGroup (hex zer negativeSign) = G.permSwapLowMid
asGroup (hex pos negativeSign) = G.permSwapLowHigh

fromGroup : G.TriPermutation → Hex
fromGroup G.permIdentity = hex neg positiveSign
fromGroup G.permRotate = hex zer positiveSign
fromGroup G.permRotate2 = hex pos positiveSign
fromGroup G.permSwapMidHigh = hex neg negativeSign
fromGroup G.permSwapLowMid = hex zer negativeSign
fromGroup G.permSwapLowHigh = hex pos negativeSign

groupRoundTrip : ∀ h → fromGroup (asGroup h) ≡ h
groupRoundTrip (hex neg positiveSign) = refl
groupRoundTrip (hex neg negativeSign) = refl
groupRoundTrip (hex zer positiveSign) = refl
groupRoundTrip (hex zer negativeSign) = refl
groupRoundTrip (hex pos positiveSign) = refl
groupRoundTrip (hex pos negativeSign) = refl

hexRoundTrip : ∀ g → asGroup (fromGroup g) ≡ g
hexRoundTrip G.permIdentity = refl
hexRoundTrip G.permRotate = refl
hexRoundTrip G.permRotate2 = refl
hexRoundTrip G.permSwapMidHigh = refl
hexRoundTrip G.permSwapLowHigh = refl
hexRoundTrip G.permSwapLowMid = refl

-- Ordered distinct pair from the original actual ternary value action.
data DistinctPair : Set where
  lowMid lowHigh midLow midHigh highLow highMid : DistinctPair

pair : G.TriPermutation → DistinctPair
pair G.permIdentity = lowMid
pair G.permRotate = midHigh
pair G.permRotate2 = highLow
pair G.permSwapLowMid = midLow
pair G.permSwapLowHigh = highMid
pair G.permSwapMidHigh = lowHigh

unpair : DistinctPair → G.TriPermutation
unpair lowMid = G.permIdentity
unpair lowHigh = G.permSwapMidHigh
unpair midLow = G.permSwapLowMid
unpair midHigh = G.permRotate
unpair highLow = G.permRotate2
unpair highMid = G.permSwapLowHigh

pairRoundTrip : ∀ g → unpair (pair g) ≡ g
pairRoundTrip G.permIdentity = refl
pairRoundTrip G.permRotate = refl
pairRoundTrip G.permRotate2 = refl
pairRoundTrip G.permSwapMidHigh = refl
pairRoundTrip G.permSwapLowHigh = refl
pairRoundTrip G.permSwapLowMid = refl

pairInverse : ∀ p → pair (unpair p) ≡ p
pairInverse lowMid = refl
pairInverse lowHigh = refl
pairInverse midLow = refl
pairInverse midHigh = refl
pairInverse highLow = refl
pairInverse highMid = refl

first second : DistinctPair → Base.TriTruth
first lowMid = Base.tri-low
first lowHigh = Base.tri-low
first midLow = Base.tri-mid
first midHigh = Base.tri-mid
first highLow = Base.tri-high
first highMid = Base.tri-high
second lowMid = Base.tri-mid
second lowHigh = Base.tri-high
second midLow = Base.tri-low
second midHigh = Base.tri-high
second highLow = Base.tri-low
second highMid = Base.tri-mid

pairFirst : ∀ g → first (pair g) ≡ G.applyPermutation g Base.tri-low
pairFirst G.permIdentity = refl
pairFirst G.permRotate = refl
pairFirst G.permRotate2 = refl
pairFirst G.permSwapMidHigh = refl
pairFirst G.permSwapLowHigh = refl
pairFirst G.permSwapLowMid = refl

pairSecond : ∀ g → second (pair g) ≡ G.applyPermutation g Base.tri-mid
pairSecond G.permIdentity = refl
pairSecond G.permRotate = refl
pairSecond G.permRotate2 = refl
pairSecond G.permSwapMidHigh = refl
pairSecond G.permSwapLowHigh = refl
pairSecond G.permSwapLowMid = refl

-- Pointed completion collapses the ENTIRE constant diagonal.
-- A literal retained zero is not invariant under value-S3.
collapse : Base.TriTruth → Base.TriTruth → Seven
collapse Base.tri-low Base.tri-low = centre
collapse Base.tri-mid Base.tri-mid = centre
collapse Base.tri-high Base.tri-high = centre
collapse Base.tri-low Base.tri-mid = active (fromGroup (unpair lowMid))
collapse Base.tri-low Base.tri-high = active (fromGroup (unpair lowHigh))
collapse Base.tri-mid Base.tri-low = active (fromGroup (unpair midLow))
collapse Base.tri-mid Base.tri-high = active (fromGroup (unpair midHigh))
collapse Base.tri-high Base.tri-low = active (fromGroup (unpair highLow))
collapse Base.tri-high Base.tri-mid = active (fromGroup (unpair highMid))

actHex : G.TriPermutation → Hex → Hex
actHex g h = fromGroup (g ∙ asGroup h)

actSeven : G.TriPermutation → Seven → Seven
actSeven g centre = centre
actSeven g (active h) = active (actHex g h)

collapseEquivariant : ∀ g x y →
  collapse (G.applyPermutation g x) (G.applyPermutation g y) ≡ actSeven g (collapse x y)
collapseEquivariant G.permIdentity Base.tri-low Base.tri-low = refl
collapseEquivariant G.permIdentity Base.tri-low Base.tri-mid = refl
collapseEquivariant G.permIdentity Base.tri-low Base.tri-high = refl
collapseEquivariant G.permIdentity Base.tri-mid Base.tri-low = refl
collapseEquivariant G.permIdentity Base.tri-mid Base.tri-mid = refl
collapseEquivariant G.permIdentity Base.tri-mid Base.tri-high = refl
collapseEquivariant G.permIdentity Base.tri-high Base.tri-low = refl
collapseEquivariant G.permIdentity Base.tri-high Base.tri-mid = refl
collapseEquivariant G.permIdentity Base.tri-high Base.tri-high = refl
collapseEquivariant G.permRotate Base.tri-low Base.tri-low = refl
collapseEquivariant G.permRotate Base.tri-low Base.tri-mid = refl
collapseEquivariant G.permRotate Base.tri-low Base.tri-high = refl
collapseEquivariant G.permRotate Base.tri-mid Base.tri-low = refl
collapseEquivariant G.permRotate Base.tri-mid Base.tri-mid = refl
collapseEquivariant G.permRotate Base.tri-mid Base.tri-high = refl
collapseEquivariant G.permRotate Base.tri-high Base.tri-low = refl
collapseEquivariant G.permRotate Base.tri-high Base.tri-mid = refl
collapseEquivariant G.permRotate Base.tri-high Base.tri-high = refl
collapseEquivariant G.permRotate2 Base.tri-low Base.tri-low = refl
collapseEquivariant G.permRotate2 Base.tri-low Base.tri-mid = refl
collapseEquivariant G.permRotate2 Base.tri-low Base.tri-high = refl
collapseEquivariant G.permRotate2 Base.tri-mid Base.tri-low = refl
collapseEquivariant G.permRotate2 Base.tri-mid Base.tri-mid = refl
collapseEquivariant G.permRotate2 Base.tri-mid Base.tri-high = refl
collapseEquivariant G.permRotate2 Base.tri-high Base.tri-low = refl
collapseEquivariant G.permRotate2 Base.tri-high Base.tri-mid = refl
collapseEquivariant G.permRotate2 Base.tri-high Base.tri-high = refl
collapseEquivariant G.permSwapMidHigh Base.tri-low Base.tri-low = refl
collapseEquivariant G.permSwapMidHigh Base.tri-low Base.tri-mid = refl
collapseEquivariant G.permSwapMidHigh Base.tri-low Base.tri-high = refl
collapseEquivariant G.permSwapMidHigh Base.tri-mid Base.tri-low = refl
collapseEquivariant G.permSwapMidHigh Base.tri-mid Base.tri-mid = refl
collapseEquivariant G.permSwapMidHigh Base.tri-mid Base.tri-high = refl
collapseEquivariant G.permSwapMidHigh Base.tri-high Base.tri-low = refl
collapseEquivariant G.permSwapMidHigh Base.tri-high Base.tri-mid = refl
collapseEquivariant G.permSwapMidHigh Base.tri-high Base.tri-high = refl
collapseEquivariant G.permSwapLowHigh Base.tri-low Base.tri-low = refl
collapseEquivariant G.permSwapLowHigh Base.tri-low Base.tri-mid = refl
collapseEquivariant G.permSwapLowHigh Base.tri-low Base.tri-high = refl
collapseEquivariant G.permSwapLowHigh Base.tri-mid Base.tri-low = refl
collapseEquivariant G.permSwapLowHigh Base.tri-mid Base.tri-mid = refl
collapseEquivariant G.permSwapLowHigh Base.tri-mid Base.tri-high = refl
collapseEquivariant G.permSwapLowHigh Base.tri-high Base.tri-low = refl
collapseEquivariant G.permSwapLowHigh Base.tri-high Base.tri-mid = refl
collapseEquivariant G.permSwapLowHigh Base.tri-high Base.tri-high = refl
collapseEquivariant G.permSwapLowMid Base.tri-low Base.tri-low = refl
collapseEquivariant G.permSwapLowMid Base.tri-low Base.tri-mid = refl
collapseEquivariant G.permSwapLowMid Base.tri-low Base.tri-high = refl
collapseEquivariant G.permSwapLowMid Base.tri-mid Base.tri-low = refl
collapseEquivariant G.permSwapLowMid Base.tri-mid Base.tri-mid = refl
collapseEquivariant G.permSwapLowMid Base.tri-mid Base.tri-high = refl
collapseEquivariant G.permSwapLowMid Base.tri-high Base.tri-low = refl
collapseEquivariant G.permSwapLowMid Base.tri-high Base.tri-mid = refl
collapseEquivariant G.permSwapLowMid Base.tri-high Base.tri-high = refl

-- The earlier 'split' was not a bijection. This is the actual product.
join : Seven → Hex → Word42
join centre h = one h
join (active k) h = two k h

cut : Word42 → Seven × Hex
cut (one h) = centre , h
cut (two k h) = active k , h

uncut : Seven × Hex → Word42
uncut (b , h) = join b h

cutJoin : ∀ b h → cut (join b h) ≡ (b , h)
cutJoin centre h = refl
cutJoin (active k) h = refl

joinCut : ∀ w → uncut (cut w) ≡ w
joinCut (one h) = refl
joinCut (two k h) = refl

act : G.TriPermutation → Word42 → Word42
act g (one h) = one (actHex g h)
act g (two k h) = two k (actHex g h)

actHexComposition : ∀ g h k → actHex g (actHex h k) ≡ actHex (g ∙ h) k
actHexComposition g h k =
  trans (cong (λ j → fromGroup (g ∙ j)) (hexRoundTrip (h ∙ asGroup k)))
        (cong fromGroup (Laws.compositionAssociative g h (asGroup k)))

actComposition : ∀ g h w → act g (act h w) ≡ act (g ∙ h) w
actComposition g h (one k) = cong one (actHexComposition g h k)
actComposition g h (two b k) = cong (two b) (actHexComposition g h k)

actHexIdentity : ∀ h → actHex G.permIdentity h ≡ h
actHexIdentity h = trans (cong fromGroup (Laws.compositionIdentityLeft (asGroup h))) (groupRoundTrip h)

actIdentity : ∀ w → act G.permIdentity w ≡ w
actIdentity (one h) = cong one (actHexIdentity h)
actIdentity (two k h) = cong (two k) (actHexIdentity h)

actInverse : ∀ g w → act (G.inversePermutation g) (act g w) ≡ w
actInverse g w = trans (actComposition (G.inversePermutation g) g w)
  (trans (cong (λ h → act h w) (Laws.compositionInverseLeft g)) (actIdentity w))

actPointed : G.TriPermutation → Word43 → Word43
actPointed g empty = empty
actPointed g (live w) = live (act g w)

pointedComposition : ∀ g h w → actPointed g (actPointed h w) ≡ actPointed (g ∙ h) w
pointedComposition g h empty = refl
pointedComposition g h (live w) = cong live (actComposition g h w)

-- The first-letter antipode implements b -> -b mod 7 in the old
-- indexing (b=1+2*t+s). Twist only on the negative final fibre.
baseAntipode : Hex → Hex
baseAntipode (hex t s) = hex (inv t) (invertSign s)

twist : Word42 → Word42
twist (one h) = one h
twist (two k (hex t positiveSign)) = two k (hex t positiveSign)
twist (two k (hex t negativeSign)) = two (baseAntipode k) (hex t negativeSign)

twistTwice : ∀ w → twist (twist w) ≡ w
twistTwice (one (hex neg positiveSign)) = refl
twistTwice (one (hex neg negativeSign)) = refl
twistTwice (one (hex zer positiveSign)) = refl
twistTwice (one (hex zer negativeSign)) = refl
twistTwice (one (hex pos positiveSign)) = refl
twistTwice (one (hex pos negativeSign)) = refl
twistTwice (two (hex neg positiveSign) (hex neg positiveSign)) = refl
twistTwice (two (hex neg positiveSign) (hex neg negativeSign)) = refl
twistTwice (two (hex neg positiveSign) (hex zer positiveSign)) = refl
twistTwice (two (hex neg positiveSign) (hex zer negativeSign)) = refl
twistTwice (two (hex neg positiveSign) (hex pos positiveSign)) = refl
twistTwice (two (hex neg positiveSign) (hex pos negativeSign)) = refl
twistTwice (two (hex neg negativeSign) (hex neg positiveSign)) = refl
twistTwice (two (hex neg negativeSign) (hex neg negativeSign)) = refl
twistTwice (two (hex neg negativeSign) (hex zer positiveSign)) = refl
twistTwice (two (hex neg negativeSign) (hex zer negativeSign)) = refl
twistTwice (two (hex neg negativeSign) (hex pos positiveSign)) = refl
twistTwice (two (hex neg negativeSign) (hex pos negativeSign)) = refl
twistTwice (two (hex zer positiveSign) (hex neg positiveSign)) = refl
twistTwice (two (hex zer positiveSign) (hex neg negativeSign)) = refl
twistTwice (two (hex zer positiveSign) (hex zer positiveSign)) = refl
twistTwice (two (hex zer positiveSign) (hex zer negativeSign)) = refl
twistTwice (two (hex zer positiveSign) (hex pos positiveSign)) = refl
twistTwice (two (hex zer positiveSign) (hex pos negativeSign)) = refl
twistTwice (two (hex zer negativeSign) (hex neg positiveSign)) = refl
twistTwice (two (hex zer negativeSign) (hex neg negativeSign)) = refl
twistTwice (two (hex zer negativeSign) (hex zer positiveSign)) = refl
twistTwice (two (hex zer negativeSign) (hex zer negativeSign)) = refl
twistTwice (two (hex zer negativeSign) (hex pos positiveSign)) = refl
twistTwice (two (hex zer negativeSign) (hex pos negativeSign)) = refl
twistTwice (two (hex pos positiveSign) (hex neg positiveSign)) = refl
twistTwice (two (hex pos positiveSign) (hex neg negativeSign)) = refl
twistTwice (two (hex pos positiveSign) (hex zer positiveSign)) = refl
twistTwice (two (hex pos positiveSign) (hex zer negativeSign)) = refl
twistTwice (two (hex pos positiveSign) (hex pos positiveSign)) = refl
twistTwice (two (hex pos positiveSign) (hex pos negativeSign)) = refl
twistTwice (two (hex pos negativeSign) (hex neg positiveSign)) = refl
twistTwice (two (hex pos negativeSign) (hex neg negativeSign)) = refl
twistTwice (two (hex pos negativeSign) (hex zer positiveSign)) = refl
twistTwice (two (hex pos negativeSign) (hex zer negativeSign)) = refl
twistTwice (two (hex pos negativeSign) (hex pos positiveSign)) = refl
twistTwice (two (hex pos negativeSign) (hex pos negativeSign)) = refl

encode : Word42 → Fin 42
encode w = W.encode (twist w)

decode : Fin 42 → Word42
decode e = twist (W.decode e)

encodeDecode : ∀ e → encode (decode e) ≡ e
encodeDecode e = trans (cong W.encode (twistTwice (W.decode e))) (W.encodeDecode e)

decodeEncode : ∀ w → decode (encode w) ≡ w
decodeEncode w = trans (cong twist (W.decodeEncode (twist w))) (twistTwice w)

rotate reflect : Word42 → Word42
rotate = act G.permRotate
reflect = act G.permSwapMidHigh

rotationRead : ∀ w → Torus.unitLabel (encode (rotate w)) ≡ (6 * Torus.unitLabel (encode w)) % 43
rotationRead (one (hex neg positiveSign)) = refl
rotationRead (one (hex neg negativeSign)) = refl
rotationRead (one (hex zer positiveSign)) = refl
rotationRead (one (hex zer negativeSign)) = refl
rotationRead (one (hex pos positiveSign)) = refl
rotationRead (one (hex pos negativeSign)) = refl
rotationRead (two (hex neg positiveSign) (hex neg positiveSign)) = refl
rotationRead (two (hex neg positiveSign) (hex neg negativeSign)) = refl
rotationRead (two (hex neg positiveSign) (hex zer positiveSign)) = refl
rotationRead (two (hex neg positiveSign) (hex zer negativeSign)) = refl
rotationRead (two (hex neg positiveSign) (hex pos positiveSign)) = refl
rotationRead (two (hex neg positiveSign) (hex pos negativeSign)) = refl
rotationRead (two (hex neg negativeSign) (hex neg positiveSign)) = refl
rotationRead (two (hex neg negativeSign) (hex neg negativeSign)) = refl
rotationRead (two (hex neg negativeSign) (hex zer positiveSign)) = refl
rotationRead (two (hex neg negativeSign) (hex zer negativeSign)) = refl
rotationRead (two (hex neg negativeSign) (hex pos positiveSign)) = refl
rotationRead (two (hex neg negativeSign) (hex pos negativeSign)) = refl
rotationRead (two (hex zer positiveSign) (hex neg positiveSign)) = refl
rotationRead (two (hex zer positiveSign) (hex neg negativeSign)) = refl
rotationRead (two (hex zer positiveSign) (hex zer positiveSign)) = refl
rotationRead (two (hex zer positiveSign) (hex zer negativeSign)) = refl
rotationRead (two (hex zer positiveSign) (hex pos positiveSign)) = refl
rotationRead (two (hex zer positiveSign) (hex pos negativeSign)) = refl
rotationRead (two (hex zer negativeSign) (hex neg positiveSign)) = refl
rotationRead (two (hex zer negativeSign) (hex neg negativeSign)) = refl
rotationRead (two (hex zer negativeSign) (hex zer positiveSign)) = refl
rotationRead (two (hex zer negativeSign) (hex zer negativeSign)) = refl
rotationRead (two (hex zer negativeSign) (hex pos positiveSign)) = refl
rotationRead (two (hex zer negativeSign) (hex pos negativeSign)) = refl
rotationRead (two (hex pos positiveSign) (hex neg positiveSign)) = refl
rotationRead (two (hex pos positiveSign) (hex neg negativeSign)) = refl
rotationRead (two (hex pos positiveSign) (hex zer positiveSign)) = refl
rotationRead (two (hex pos positiveSign) (hex zer negativeSign)) = refl
rotationRead (two (hex pos positiveSign) (hex pos positiveSign)) = refl
rotationRead (two (hex pos positiveSign) (hex pos negativeSign)) = refl
rotationRead (two (hex pos negativeSign) (hex neg positiveSign)) = refl
rotationRead (two (hex pos negativeSign) (hex neg negativeSign)) = refl
rotationRead (two (hex pos negativeSign) (hex zer positiveSign)) = refl
rotationRead (two (hex pos negativeSign) (hex zer negativeSign)) = refl
rotationRead (two (hex pos negativeSign) (hex pos positiveSign)) = refl
rotationRead (two (hex pos negativeSign) (hex pos negativeSign)) = refl

reflectionRead : ∀ w → (Torus.unitLabel (encode (reflect w)) * Torus.unitLabel (encode w)) % 43 ≡ 42
reflectionRead (one (hex neg positiveSign)) = refl
reflectionRead (one (hex neg negativeSign)) = refl
reflectionRead (one (hex zer positiveSign)) = refl
reflectionRead (one (hex zer negativeSign)) = refl
reflectionRead (one (hex pos positiveSign)) = refl
reflectionRead (one (hex pos negativeSign)) = refl
reflectionRead (two (hex neg positiveSign) (hex neg positiveSign)) = refl
reflectionRead (two (hex neg positiveSign) (hex neg negativeSign)) = refl
reflectionRead (two (hex neg positiveSign) (hex zer positiveSign)) = refl
reflectionRead (two (hex neg positiveSign) (hex zer negativeSign)) = refl
reflectionRead (two (hex neg positiveSign) (hex pos positiveSign)) = refl
reflectionRead (two (hex neg positiveSign) (hex pos negativeSign)) = refl
reflectionRead (two (hex neg negativeSign) (hex neg positiveSign)) = refl
reflectionRead (two (hex neg negativeSign) (hex neg negativeSign)) = refl
reflectionRead (two (hex neg negativeSign) (hex zer positiveSign)) = refl
reflectionRead (two (hex neg negativeSign) (hex zer negativeSign)) = refl
reflectionRead (two (hex neg negativeSign) (hex pos positiveSign)) = refl
reflectionRead (two (hex neg negativeSign) (hex pos negativeSign)) = refl
reflectionRead (two (hex zer positiveSign) (hex neg positiveSign)) = refl
reflectionRead (two (hex zer positiveSign) (hex neg negativeSign)) = refl
reflectionRead (two (hex zer positiveSign) (hex zer positiveSign)) = refl
reflectionRead (two (hex zer positiveSign) (hex zer negativeSign)) = refl
reflectionRead (two (hex zer positiveSign) (hex pos positiveSign)) = refl
reflectionRead (two (hex zer positiveSign) (hex pos negativeSign)) = refl
reflectionRead (two (hex zer negativeSign) (hex neg positiveSign)) = refl
reflectionRead (two (hex zer negativeSign) (hex neg negativeSign)) = refl
reflectionRead (two (hex zer negativeSign) (hex zer positiveSign)) = refl
reflectionRead (two (hex zer negativeSign) (hex zer negativeSign)) = refl
reflectionRead (two (hex zer negativeSign) (hex pos positiveSign)) = refl
reflectionRead (two (hex zer negativeSign) (hex pos negativeSign)) = refl
reflectionRead (two (hex pos positiveSign) (hex neg positiveSign)) = refl
reflectionRead (two (hex pos positiveSign) (hex neg negativeSign)) = refl
reflectionRead (two (hex pos positiveSign) (hex zer positiveSign)) = refl
reflectionRead (two (hex pos positiveSign) (hex zer negativeSign)) = refl
reflectionRead (two (hex pos positiveSign) (hex pos positiveSign)) = refl
reflectionRead (two (hex pos positiveSign) (hex pos negativeSign)) = refl
reflectionRead (two (hex pos negativeSign) (hex neg positiveSign)) = refl
reflectionRead (two (hex pos negativeSign) (hex neg negativeSign)) = refl
reflectionRead (two (hex pos negativeSign) (hex zer positiveSign)) = refl
reflectionRead (two (hex pos negativeSign) (hex zer negativeSign)) = refl
reflectionRead (two (hex pos negativeSign) (hex pos positiveSign)) = refl
reflectionRead (two (hex pos negativeSign) (hex pos negativeSign)) = refl

reflectionExponent : ∀ w → (toℕ (encode (reflect w)) + toℕ (encode w)) % 42 ≡ 21
reflectionExponent (one (hex neg positiveSign)) = refl
reflectionExponent (one (hex neg negativeSign)) = refl
reflectionExponent (one (hex zer positiveSign)) = refl
reflectionExponent (one (hex zer negativeSign)) = refl
reflectionExponent (one (hex pos positiveSign)) = refl
reflectionExponent (one (hex pos negativeSign)) = refl
reflectionExponent (two (hex neg positiveSign) (hex neg positiveSign)) = refl
reflectionExponent (two (hex neg positiveSign) (hex neg negativeSign)) = refl
reflectionExponent (two (hex neg positiveSign) (hex zer positiveSign)) = refl
reflectionExponent (two (hex neg positiveSign) (hex zer negativeSign)) = refl
reflectionExponent (two (hex neg positiveSign) (hex pos positiveSign)) = refl
reflectionExponent (two (hex neg positiveSign) (hex pos negativeSign)) = refl
reflectionExponent (two (hex neg negativeSign) (hex neg positiveSign)) = refl
reflectionExponent (two (hex neg negativeSign) (hex neg negativeSign)) = refl
reflectionExponent (two (hex neg negativeSign) (hex zer positiveSign)) = refl
reflectionExponent (two (hex neg negativeSign) (hex zer negativeSign)) = refl
reflectionExponent (two (hex neg negativeSign) (hex pos positiveSign)) = refl
reflectionExponent (two (hex neg negativeSign) (hex pos negativeSign)) = refl
reflectionExponent (two (hex zer positiveSign) (hex neg positiveSign)) = refl
reflectionExponent (two (hex zer positiveSign) (hex neg negativeSign)) = refl
reflectionExponent (two (hex zer positiveSign) (hex zer positiveSign)) = refl
reflectionExponent (two (hex zer positiveSign) (hex zer negativeSign)) = refl
reflectionExponent (two (hex zer positiveSign) (hex pos positiveSign)) = refl
reflectionExponent (two (hex zer positiveSign) (hex pos negativeSign)) = refl
reflectionExponent (two (hex zer negativeSign) (hex neg positiveSign)) = refl
reflectionExponent (two (hex zer negativeSign) (hex neg negativeSign)) = refl
reflectionExponent (two (hex zer negativeSign) (hex zer positiveSign)) = refl
reflectionExponent (two (hex zer negativeSign) (hex zer negativeSign)) = refl
reflectionExponent (two (hex zer negativeSign) (hex pos positiveSign)) = refl
reflectionExponent (two (hex zer negativeSign) (hex pos negativeSign)) = refl
reflectionExponent (two (hex pos positiveSign) (hex neg positiveSign)) = refl
reflectionExponent (two (hex pos positiveSign) (hex neg negativeSign)) = refl
reflectionExponent (two (hex pos positiveSign) (hex zer positiveSign)) = refl
reflectionExponent (two (hex pos positiveSign) (hex zer negativeSign)) = refl
reflectionExponent (two (hex pos positiveSign) (hex pos positiveSign)) = refl
reflectionExponent (two (hex pos positiveSign) (hex pos negativeSign)) = refl
reflectionExponent (two (hex pos negativeSign) (hex neg positiveSign)) = refl
reflectionExponent (two (hex pos negativeSign) (hex neg negativeSign)) = refl
reflectionExponent (two (hex pos negativeSign) (hex zer positiveSign)) = refl
reflectionExponent (two (hex pos negativeSign) (hex zer negativeSign)) = refl
reflectionExponent (two (hex pos negativeSign) (hex pos positiveSign)) = refl
reflectionExponent (two (hex pos negativeSign) (hex pos negativeSign)) = refl

reflectionConjugatesRotation : ∀ w → reflect (rotate (reflect w)) ≡ act G.permRotate2 w
reflectionConjugatesRotation w =
  trans (actComposition G.permSwapMidHigh G.permRotate (reflect w))
        (actComposition (G.permSwapMidHigh ∙ G.permRotate) G.permSwapMidHigh w)

-- Chart map into the same original Fin42 lattice rows.
chart : Word42 → Fin 42
chart w = Torus.decode (encode w)

unChart : Fin 42 → Word42
unChart k = decode (Torus.encode k)

chartRoundTrip : ∀ w → unChart (chart w) ≡ w
chartRoundTrip w = trans (cong decode (Torus.encodeDecode (encode w))) (decodeEncode w)

wordRoundTrip : ∀ k → chart (unChart k) ≡ k
wordRoundTrip k = trans (cong Torus.decode (encodeDecode (Torus.encode k))) (Torus.decodeEncode k)

-- Torus normalizer: row [x:y] -> [x:-y] gives e -> -e.
-- The additional torus half-turn makes e -> 21-e free.
-- Original product transport uses actual reindex theorem, no analytic
-- invariance of individual chart values is asserted.
sameProduct : (f : Fin 42 → C.BishopComplex) →
  C._≈C_ (Prod.product (λ e → f (chart (decode e)))) (Prod.product f)
sameProduct f = Prod.reindex f (λ e → chart (decode e))
  (λ k → encode (unChart k))
  (λ e → trans (cong encode (chartRoundTrip (decode e))) (encodeDecode e))
  (λ k → trans (cong chart (decodeEncode (unChart k))) (wordRoundTrip k))

-- Direct scalar flip from the OLD cyclic carrier commutes with rotation;
-- the true S3 reflection instead inverts it. The following is a concrete
-- no-identification witness on the common underlying word.
cyclicCommutesAtSeed :
  W.flip (W.rotate (one (hex neg positiveSign))) ≡
  W.rotate (W.flip (one (hex neg positiveSign)))
cyclicCommutesAtSeed = refl

nonabelianAtSeed :
  reflect (rotate (one (hex neg positiveSign))) ≡
  rotate (reflect (one (hex neg positiveSign))) → ⊥
nonabelianAtSeed ()
