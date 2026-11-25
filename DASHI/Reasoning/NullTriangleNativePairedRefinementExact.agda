module DASHI.Reasoning.NullTriangleNativePairedRefinementExact where

-- Actual ordered Trit vectors and the original H05 observer. A single
-- trit prepend changes pair alignment; a paired prepend is the address
-- operation for one ramified uniformizer step. No field equality is
-- manufactured by this address proof.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (Vec; []; _∷_)
open import DASHI.Algebra.Trit using (Trit)
import DASHI.Reasoning.NullTriangleOrderedUltrametricCubeExact as P
import DASHI.Reasoning.NullTriangleNativeH05ObserverExact as H
import DASHI.Reasoning.Trialectic369HypervoxelUltrametricExact as V

evenLength oddLength : Nat → Nat
evenLength zero = zero
evenLength (suc n) = suc (suc (evenLength n))
oddLength zero = 1
oddLength (suc n) = suc (suc (oddLength n))

packEven : ∀ {n} → Vec Trit (evenLength n) → Vec P.Point n
packEven {zero} [] = []
packEven {suc n} (x ∷ y ∷ v) = (x ∷ y ∷ []) ∷ packEven {n} v

unpackEven : ∀ {n} → Vec P.Point n → Vec Trit (evenLength n)
unpackEven [] = []
unpackEven ((x ∷ y ∷ []) ∷ ds) = x ∷ y ∷ unpackEven ds

unpackPackEven : ∀ {n} (v : Vec Trit (evenLength n)) →
  unpackEven (packEven {n} v) ≡ v
unpackPackEven {zero} [] = refl
unpackPackEven {suc n} (x ∷ y ∷ v) =
  cong (λ w → x ∷ y ∷ w) (unpackPackEven {n} v)

packUnpackEven : ∀ {n} (ds : Vec P.Point n) →
  packEven {n} (unpackEven ds) ≡ ds
packUnpackEven [] = refl
packUnpackEven ((x ∷ y ∷ []) ∷ ds) =
  cong ((x ∷ y ∷ []) ∷_) (packUnpackEven ds)

packOdd : ∀ {n} → Vec Trit (oddLength n) → Vec P.Point n × Trit
packOdd {zero} (t ∷ []) = [] , t
packOdd {suc n} (x ∷ y ∷ v) with packOdd {n} v
... | ds , t = (x ∷ y ∷ []) ∷ ds , t

unpackOdd : ∀ {n} → Vec P.Point n × Trit → Vec Trit (oddLength n)
unpackOdd ([] , t) = t ∷ []
unpackOdd ((x ∷ y ∷ []) ∷ ds , t) = x ∷ y ∷ unpackOdd (ds , t)

unpackPackOdd : ∀ {n} (v : Vec Trit (oddLength n)) →
  unpackOdd (packOdd {n} v) ≡ v
unpackPackOdd {zero} (t ∷ []) = refl
unpackPackOdd {suc n} (x ∷ y ∷ v)
  with packOdd {n} v | unpackPackOdd {n} v
... | ds , t | eq = cong (λ w → x ∷ y ∷ w) eq

packUnpackOdd : ∀ {n} (ds : Vec P.Point n) (t : Trit) →
  packOdd {n} (unpackOdd (ds , t)) ≡ (ds , t)
packUnpackOdd [] t = refl
packUnpackOdd ((x ∷ y ∷ []) ∷ ds) t
  rewrite packUnpackOdd ds t = refl

-- The last ninth trit is an actual coordinate, not a discarded zero.
observerPairs : H.Observer → Vec P.Point 4 × Trit
observerPairs o = packOdd {4} (H.to o)

pairsObserver : Vec P.Point 4 × Trit → H.Observer
pairsObserver v = H.from (unpackOdd v)

observerPairsInverse : ∀ o → pairsObserver (observerPairs o) ≡ o
observerPairsInverse o =
  trans (cong H.from (unpackPackOdd {4} (H.to o)))
        (V.observerVecRoundTrip o)

pairsObserverInverse : ∀ ds t → observerPairs (pairsObserver (ds , t)) ≡ (ds , t)
pairsObserverInverse ds t =
  trans (cong (packOdd {4}) (V.vecObserverRoundTrip (unpackOdd (ds , t))))
        (packUnpackOdd ds t)

-- Compare the actual one-trit H05 refinement with the correct pair alignment.
singlePrefixRecharts : ∀ t a b c d e f g h j →
  packEven {5} (t ∷ a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ j ∷ []) ≡
  (t ∷ a ∷ []) ∷ (b ∷ c ∷ []) ∷ (d ∷ e ∷ []) ∷
  (f ∷ g ∷ []) ∷ (h ∷ j ∷ []) ∷ []
singlePrefixRecharts t a b c d e f g h j = refl

-- Arbitrary-depth aligned prefix; this is exactly the digit operation
-- corresponding to r + pi*z in the existing classical field proof.
pairedPrefix : ∀ {n} (x y : Trit) (ds : Vec P.Point n) (t : Trit) →
  packOdd {suc n} (x ∷ y ∷ unpackOdd (ds , t)) ≡ ((x ∷ y ∷ []) ∷ ds , t)
pairedPrefix x y ds t = packUnpackOdd ((x ∷ y ∷ []) ∷ ds) t
