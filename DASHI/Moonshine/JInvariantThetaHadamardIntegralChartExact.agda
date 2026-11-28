module DASHI.Moonshine.JInvariantThetaHadamardIntegralChartExact where

-- Classical D4 / Sylvester Hadamard transform. Direct donor:
-- Integration/Paper9ThetaHadamardGeometry.lean (dashi_lean4 c335955cc5c6).
-- Existing DASHI finite Walsh inversion and NS Walsh Parseval motivate the
-- same unnormalised sign transform; their rational/8- or 16-coordinate
-- carriers do not supply integral parity divisibility on D4.
-- This module uses division-free affine charts; no new theta histories.
-- SOURCE-WRITTEN, kernel pending.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; _+_; _-_; _*_)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; _:=_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

record Quad : Set where
  constructor quad
  field a b c d : ℤ
open Quad public

quadCong : ∀ {a b c d e f g h} → a ≡ e → b ≡ f → c ≡ g → d ≡ h →
  quad a b c d ≡ quad e f g h
quadCong refl refl refl refl = refl

H : Quad → Quad
H (quad a b c d) = quad ((((a + b) + c) + d)) ((((a + b) - c) - d)) ((((a - b) + c) - d)) ((((a - b) - c) + d))

flip : Quad → Quad
flip (quad a b c d) = quad (((+ 0) - a)) (b) (c) (d)

integerOdd : Quad → Quad
integerOdd (quad k b c d) = quad (((((((+ 2) * k) + (+ 1)) - b) - c) - d)) (b) (c) (d)

halfEven : Quad → Quad
halfEven (quad j u v w) = quad ((((+ 2) * u) + (+ 1))) ((((+ 2) * v) + (+ 1))) ((((+ 2) * w) + (+ 1))) (((((((+ 4) * j) + (+ 0)) - (((+ 2) * u) + (+ 1))) - (((+ 2) * v) + (+ 1))) - (((+ 2) * w) + (+ 1))))

halfOdd : Quad → Quad
halfOdd (quad j u v w) = quad ((((+ 2) * u) + (+ 1))) ((((+ 2) * v) + (+ 1))) ((((+ 2) * w) + (+ 1))) (((((((+ 4) * j) + (+ 2)) - (((+ 2) * u) + (+ 1))) - (((+ 2) * v) + (+ 1))) - (((+ 2) * w) + (+ 1))))

encode : Quad → Quad
encode (quad k b c d) = quad (((((((+ 2) * k) + (+ 1)) - b) - c) - d)) (k) (((k - c) - d)) (((k - b) - d))

decode : Quad → Quad
decode (quad j u v w) = quad (u) ((((u + v) + (+ 1)) - j)) ((((u + w) + (+ 1)) - j)) ((((j - v) - w) - (+ 1)))

flipToOdd : Quad → Quad
flipToOdd (quad j u v w) = quad (((j - u) - (+ 1))) ((((+ 0) - u) - (+ 1))) (v) (w)

flipToEven : Quad → Quad
flipToEven (quad j u v w) = quad ((j - u)) ((((+ 0) - u) - (+ 1))) (v) (w)

normSq : Quad → ℤ
normSq (quad a b c d) = ((((a * a) + (b * b)) + (c * c)) + (d * d))

encodeDecode : ∀ x → encode (decode x) ≡ x
encodeDecode (quad j u v w) = quadCong
  (solve 4 (λ j u v w → (((((con (+ 2) :* u) :+ con (+ 1)) :- (((u :+ v) :+ con (+ 1)) :- j)) :- (((u :+ w) :+ con (+ 1)) :- j)) :- (((j :- v) :- w) :- con (+ 1))) := j) refl j u v w)
  (solve 4 (λ j u v w → u := u) refl j u v w)
  (solve 4 (λ j u v w → ((u :- (((u :+ w) :+ con (+ 1)) :- j)) :- (((j :- v) :- w) :- con (+ 1))) := v) refl j u v w)
  (solve 4 (λ j u v w → ((u :- (((u :+ v) :+ con (+ 1)) :- j)) :- (((j :- v) :- w) :- con (+ 1))) := w) refl j u v w)

decodeEncode : ∀ x → decode (encode x) ≡ x
decodeEncode (quad k b c d) = quadCong
  (solve 4 (λ k b c d → k := k) refl k b c d)
  (solve 4 (λ k b c d → (((k :+ ((k :- c) :- d)) :+ con (+ 1)) :- (((((con (+ 2) :* k) :+ con (+ 1)) :- b) :- c) :- d)) := b) refl k b c d)
  (solve 4 (λ k b c d → (((k :+ ((k :- b) :- d)) :+ con (+ 1)) :- (((((con (+ 2) :* k) :+ con (+ 1)) :- b) :- c) :- d)) := c) refl k b c d)
  (solve 4 (λ k b c d → ((((((((con (+ 2) :* k) :+ con (+ 1)) :- b) :- c) :- d) :- ((k :- c) :- d)) :- ((k :- b) :- d)) :- con (+ 1)) := d) refl k b c d)

flipDecode : ∀ x → flipToEven (flipToOdd x) ≡ x
flipDecode (quad j u v w) = quadCong
  (solve 4 (λ j u v w → (((j :- u) :- con (+ 1)) :- ((con (+ 0) :- u) :- con (+ 1))) := j) refl j u v w)
  (solve 4 (λ j u v w → ((con (+ 0) :- ((con (+ 0) :- u) :- con (+ 1))) :- con (+ 1)) := u) refl j u v w)
  (solve 4 (λ j u v w → v := v) refl j u v w)
  (solve 4 (λ j u v w → w := w) refl j u v w)

flipEncode : ∀ x → flipToOdd (flipToEven x) ≡ x
flipEncode (quad j u v w) = quadCong
  (solve 4 (λ j u v w → (((j :- u) :- ((con (+ 0) :- u) :- con (+ 1))) :- con (+ 1)) := j) refl j u v w)
  (solve 4 (λ j u v w → ((con (+ 0) :- ((con (+ 0) :- u) :- con (+ 1))) :- con (+ 1)) := u) refl j u v w)
  (solve 4 (λ j u v w → v := v) refl j u v w)
  (solve 4 (λ j u v w → w := w) refl j u v w)

encodeRead : ∀ x → H (integerOdd x) ≡ halfEven (encode x)
encodeRead (quad k b c d) = quadCong
  (solve 4 (λ k b c d → ((((((((con (+ 2) :* k) :+ con (+ 1)) :- b) :- c) :- d) :+ b) :+ c) :+ d) := ((con (+ 2) :* k) :+ con (+ 1))) refl k b c d)
  (solve 4 (λ k b c d → ((((((((con (+ 2) :* k) :+ con (+ 1)) :- b) :- c) :- d) :+ b) :- c) :- d) := ((con (+ 2) :* ((k :- c) :- d)) :+ con (+ 1))) refl k b c d)
  (solve 4 (λ k b c d → ((((((((con (+ 2) :* k) :+ con (+ 1)) :- b) :- c) :- d) :- b) :+ c) :- d) := ((con (+ 2) :* ((k :- b) :- d)) :+ con (+ 1))) refl k b c d)
  (solve 4 (λ k b c d → ((((((((con (+ 2) :* k) :+ con (+ 1)) :- b) :- c) :- d) :- b) :- c) :+ d) := (((((con (+ 4) :* (((((con (+ 2) :* k) :+ con (+ 1)) :- b) :- c) :- d)) :+ con (+ 0)) :- ((con (+ 2) :* k) :+ con (+ 1))) :- ((con (+ 2) :* ((k :- c) :- d)) :+ con (+ 1))) :- ((con (+ 2) :* ((k :- b) :- d)) :+ con (+ 1)))) refl k b c d)

flipRead : ∀ x → flip (halfEven x) ≡ halfOdd (flipToOdd x)
flipRead (quad j u v w) = quadCong
  (solve 4 (λ j u v w → (con (+ 0) :- ((con (+ 2) :* u) :+ con (+ 1))) := ((con (+ 2) :* ((con (+ 0) :- u) :- con (+ 1))) :+ con (+ 1))) refl j u v w)
  (solve 4 (λ j u v w → ((con (+ 2) :* v) :+ con (+ 1)) := ((con (+ 2) :* v) :+ con (+ 1))) refl j u v w)
  (solve 4 (λ j u v w → ((con (+ 2) :* w) :+ con (+ 1)) := ((con (+ 2) :* w) :+ con (+ 1))) refl j u v w)
  (solve 4 (λ j u v w → (((((con (+ 4) :* j) :+ con (+ 0)) :- ((con (+ 2) :* u) :+ con (+ 1))) :- ((con (+ 2) :* v) :+ con (+ 1))) :- ((con (+ 2) :* w) :+ con (+ 1))) := (((((con (+ 4) :* ((j :- u) :- con (+ 1))) :+ con (+ 2)) :- ((con (+ 2) :* ((con (+ 0) :- u) :- con (+ 1))) :+ con (+ 1))) :- ((con (+ 2) :* v) :+ con (+ 1))) :- ((con (+ 2) :* w) :+ con (+ 1)))) refl j u v w)

inverseRead : ∀ x → H (halfEven x) ≡ quad ((+ 4) * a (integerOdd (decode x))) ((+ 4) * b (integerOdd (decode x))) ((+ 4) * c (integerOdd (decode x))) ((+ 4) * d (integerOdd (decode x)))
inverseRead (quad j u v w) = quadCong
  (solve 4 (λ j u v w → (((((con (+ 2) :* u) :+ con (+ 1)) :+ ((con (+ 2) :* v) :+ con (+ 1))) :+ ((con (+ 2) :* w) :+ con (+ 1))) :+ (((((con (+ 4) :* j) :+ con (+ 0)) :- ((con (+ 2) :* u) :+ con (+ 1))) :- ((con (+ 2) :* v) :+ con (+ 1))) :- ((con (+ 2) :* w) :+ con (+ 1)))) := (con (+ 4) :* (((((con (+ 2) :* u) :+ con (+ 1)) :- (((u :+ v) :+ con (+ 1)) :- j)) :- (((u :+ w) :+ con (+ 1)) :- j)) :- (((j :- v) :- w) :- con (+ 1))))) refl j u v w)
  (solve 4 (λ j u v w → (((((con (+ 2) :* u) :+ con (+ 1)) :+ ((con (+ 2) :* v) :+ con (+ 1))) :- ((con (+ 2) :* w) :+ con (+ 1))) :- (((((con (+ 4) :* j) :+ con (+ 0)) :- ((con (+ 2) :* u) :+ con (+ 1))) :- ((con (+ 2) :* v) :+ con (+ 1))) :- ((con (+ 2) :* w) :+ con (+ 1)))) := (con (+ 4) :* (((u :+ v) :+ con (+ 1)) :- j))) refl j u v w)
  (solve 4 (λ j u v w → (((((con (+ 2) :* u) :+ con (+ 1)) :- ((con (+ 2) :* v) :+ con (+ 1))) :+ ((con (+ 2) :* w) :+ con (+ 1))) :- (((((con (+ 4) :* j) :+ con (+ 0)) :- ((con (+ 2) :* u) :+ con (+ 1))) :- ((con (+ 2) :* v) :+ con (+ 1))) :- ((con (+ 2) :* w) :+ con (+ 1)))) := (con (+ 4) :* (((u :+ w) :+ con (+ 1)) :- j))) refl j u v w)
  (solve 4 (λ j u v w → (((((con (+ 2) :* u) :+ con (+ 1)) :- ((con (+ 2) :* v) :+ con (+ 1))) :- ((con (+ 2) :* w) :+ con (+ 1))) :+ (((((con (+ 4) :* j) :+ con (+ 0)) :- ((con (+ 2) :* u) :+ con (+ 1))) :- ((con (+ 2) :* v) :+ con (+ 1))) :- ((con (+ 2) :* w) :+ con (+ 1)))) := (con (+ 4) :* (((j :- v) :- w) :- con (+ 1)))) refl j u v w)

Hnorm : ∀ x → normSq (H x) ≡ (+ 4) * normSq x
Hnorm (quad a b c d) =
  (solve 4 (λ a b c d → (((((((a :+ b) :+ c) :+ d) :* (((a :+ b) :+ c) :+ d)) :+ ((((a :+ b) :- c) :- d) :* (((a :+ b) :- c) :- d))) :+ ((((a :- b) :+ c) :- d) :* (((a :- b) :+ c) :- d))) :+ ((((a :- b) :- c) :+ d) :* (((a :- b) :- c) :+ d))) := (con (+ 4) :* ((((a :* a) :+ (b :* b)) :+ (c :* c)) :+ (d :* d)))) refl a b c d)

flipNorm : ∀ x → normSq (flip x) ≡ normSq x
flipNorm (quad a b c d) =
  (solve 4 (λ a b c d → (((((con (+ 0) :- a) :* (con (+ 0) :- a)) :+ (b :* b)) :+ (c :* c)) :+ (d :* d)) := ((((a :* a) :+ (b :* b)) :+ (c :* c)) :+ (d :* d))) refl a b c d)

encodeNorm : ∀ x → normSq (halfEven (encode x)) ≡ (+ 4) * normSq (integerOdd x)
encodeNorm x = trans (cong normSq (sym (encodeRead x))) (Hnorm (integerOdd x))

flipGrade : ∀ x → normSq (halfOdd (flipToOdd x)) ≡ normSq (halfEven x)
flipGrade x = trans (cong normSq (sym (flipRead x))) (flipNorm (halfEven x))

-- Use the same integral norm on the odd chart and its scaled value on
-- each odd-coordinate sheet. The grade remains arbitrary, including zero.
IntegerShell : ℤ → Set
IntegerShell n = Σ Quad (λ x → (+ 4) * normSq (integerOdd x) ≡ n)

EvenShell : ℤ → Set
EvenShell n = Σ Quad (λ x → normSq (halfEven x) ≡ n)

OddShell : ℤ → Set
OddShell n = Σ Quad (λ x → normSq (halfOdd x) ≡ n)

toEven : ∀ {n} → IntegerShell n → EvenShell n
toEven (x , p) = encode x , trans (encodeNorm x) p

fromEven : ∀ {n} → EvenShell n → IntegerShell n
fromEven (x , p) = decode x ,
  trans (sym (encodeNorm (decode x)))
    (trans (cong (λ y → normSq (halfEven y)) (encodeDecode x)) p)

toOdd : ∀ {n} → EvenShell n → OddShell n
toOdd (x , p) = flipToOdd x , trans (flipGrade x) p

fromOdd : ∀ {n} → OddShell n → EvenShell n
fromOdd (x , p) = flipToEven x ,
  trans (sym (flipGrade (flipToEven x)))
    (trans (cong (λ y → normSq (halfOdd y)) (flipEncode x)) p)

-- Both directions reconstruct all coordinate data, not merely its norm.
-- Equality of dependent grade witnesses can be supplied by integer UIP.
integerRoundTrip : ∀ {n} (x : IntegerShell n) → proj₁ (fromEven (toEven x)) ≡ proj₁ x
integerRoundTrip (x , p) = decodeEncode x

evenRoundTrip : ∀ {n} (x : EvenShell n) → proj₁ (toEven (fromEven x)) ≡ proj₁ x
evenRoundTrip (x , p) = encodeDecode x

oddRoundTrip : ∀ {n} (x : OddShell n) → proj₁ (toOdd (fromOdd x)) ≡ proj₁ x
oddRoundTrip (x , p) = flipEncode x

evenFlipRoundTrip : ∀ {n} (x : EvenShell n) → proj₁ (fromOdd (toOdd x)) ≡ proj₁ x
evenFlipRoundTrip (x , p) = flipDecode x

twoCopies : ∀ {n} → IntegerShell n ⊎ IntegerShell n → EvenShell n ⊎ OddShell n
twoCopies (inj₁ x) = inj₁ (toEven x)
twoCopies (inj₂ x) = inj₂ (toOdd (toEven x))

reopen : ∀ {n} → EvenShell n ⊎ OddShell n → IntegerShell n ⊎ IntegerShell n
reopen (inj₁ x) = inj₁ (fromEven x)
reopen (inj₂ x) = inj₂ (fromEven (fromOdd x))

-- The chart-to-bounded-enumeration permutation and exact Cauchy
-- coefficient counting remain separate; no all-index count is assumed.


-- Coverage on the raw integer coordinates with explicit parity witnesses.
-- This eliminates any appeal to division rounding in the chart inversion.
total : Quad → ℤ
total (quad a b c d) = ((a + b) + c) + d

integerChart : Quad → ℤ → Quad
integerChart (quad a b c d) k = quad k b c d

integerChartRead : ∀ x k → total x ≡ (+ 2) * k + (+ 1) →
  integerOdd (integerChart x k) ≡ x
integerChartRead (quad a b c d) k h = quadCong
  (trans (cong (λ t → ((t - b) - c) - d) (sym h))
    (solve 4 (λ a b c d → (((a :+ b :+ c :+ d) :- b) :- c) :- d := a)
      refl a b c d)) refl refl refl

fourthRead : ∀ a b c d → (((a + b) + c) + d) - a - b - c ≡ d
fourthRead a b c d = solve 4
  (λ a b c d → (((a :+ b :+ c :+ d) :- a) :- b) :- c := d)
  refl a b c d

halfEvenChartRead : ∀ x j u v w →
  total x ≡ (+ 4) * j →
  a x ≡ (+ 2) * u + (+ 1) →
  b x ≡ (+ 2) * v + (+ 1) →
  c x ≡ (+ 2) * w + (+ 1) →
  halfEven (quad j u v w) ≡ x
halfEvenChartRead (quad a b c d) j u v w h ha hb hc = quadCong
  (sym ha) (sym hb) (sym hc)
  (trans (cong (λ t → t - ((+ 2) * u + (+ 1)) - ((+ 2) * v + (+ 1)) - ((+ 2) * w + (+ 1)))
    (trans (solve 1 (λ j → con (+ 4) :* j :+ con (+ 0) := con (+ 4) :* j) refl j) (sym h)))
    (trans (cong (λ t → (((a + b) + c) + d) - t - ((+ 2) * v + (+ 1)) - ((+ 2) * w + (+ 1))) (sym ha))
      (trans (cong (λ t → (((a + b) + c) + d) - a - t - ((+ 2) * w + (+ 1))) (sym hb))
        (trans (cong (λ t → (((a + b) + c) + d) - a - b - t) (sym hc))
          (fourthRead a b c d)))))

halfOddChartRead : ∀ x j u v w →
  total x ≡ (+ 4) * j + (+ 2) →
  a x ≡ (+ 2) * u + (+ 1) →
  b x ≡ (+ 2) * v + (+ 1) →
  c x ≡ (+ 2) * w + (+ 1) →
  halfOdd (quad j u v w) ≡ x
halfOddChartRead (quad a b c d) j u v w h ha hb hc = quadCong
  (sym ha) (sym hb) (sym hc)
  (trans (cong (λ t → t - ((+ 2) * u + (+ 1)) - ((+ 2) * v + (+ 1)) - ((+ 2) * w + (+ 1))) (sym h))
    (trans (cong (λ t → (((a + b) + c) + d) - t - ((+ 2) * v + (+ 1)) - ((+ 2) * w + (+ 1))) (sym ha))
      (trans (cong (λ t → (((a + b) + c) + d) - a - t - ((+ 2) * w + (+ 1))) (sym hb))
        (trans (cong (λ t → (((a + b) + c) + d) - a - b - t) (sym hc))
          (fourthRead a b c d)))))

-- Witness that the fourth raw coordinate of either half chart is odd.
halfEvenFourth : ∀ j u v w →
  d (halfEven (quad j u v w)) ≡
    (+ 2) * ((+ 2) * j - u - v - w - (+ 2)) + (+ 1)
halfEvenFourth j u v w = solve 4
  (λ j u v w →
    con (+ 4) :* j :+ con (+ 0) :- (con (+ 2) :* u :+ con (+ 1))
      :- (con (+ 2) :* v :+ con (+ 1)) :- (con (+ 2) :* w :+ con (+ 1))
    := con (+ 2) :* (con (+ 2) :* j :- u :- v :- w :- con (+ 2)) :+ con (+ 1))
  refl j u v w

halfOddFourth : ∀ j u v w →
  d (halfOdd (quad j u v w)) ≡
    (+ 2) * ((+ 2) * j - u - v - w - (+ 1)) + (+ 1)
halfOddFourth j u v w = solve 4
  (λ j u v w →
    con (+ 4) :* j :+ con (+ 2) :- (con (+ 2) :* u :+ con (+ 1))
      :- (con (+ 2) :* v :+ con (+ 1)) :- (con (+ 2) :* w :+ con (+ 1))
    := con (+ 2) :* (con (+ 2) :* j :- u :- v :- w :- con (+ 1)) :+ con (+ 1))
  refl j u v w
