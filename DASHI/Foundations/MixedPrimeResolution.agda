module DASHI.Foundations.MixedPrimeResolution where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.String using (String)

open import DASHI.Foundations.Base369BinaryTernaryRefinement using
  (Resolution23; binaryDepth; ternaryDepth; pow)

record Resolution23Q : Set where
  constructor resolution23q
  field
    binaryDepthQ : Nat
    ternaryDepthQ : Nat
    thirdBase : Nat
    thirdDepth : Nat

open Resolution23Q public

mixedSectorCount : Resolution23Q → Nat
mixedSectorCount r =
  pow 2 (binaryDepthQ r) *
  (pow 3 (ternaryDepthQ r) * pow (thirdBase r) (thirdDepth r))

fromResolution23 : Nat → Resolution23 → Resolution23Q
fromResolution23 q r = resolution23q (binaryDepth r) (ternaryDepth r) q zero

binaryRefineQ : Resolution23Q → Resolution23Q
binaryRefineQ (resolution23q a b q c) = resolution23q (suc a) b q c
ternaryRefineQ : Resolution23Q → Resolution23Q
ternaryRefineQ (resolution23q a b q c) = resolution23q a (suc b) q c
thirdRefineQ : Resolution23Q → Resolution23Q
thirdRefineQ (resolution23q a b q c) = resolution23q a b q (suc c)

binary-ternary-Q-commutes : (r : Resolution23Q) → binaryRefineQ (ternaryRefineQ r) ≡ ternaryRefineQ (binaryRefineQ r)
binary-ternary-Q-commutes (resolution23q a b q c) = refl
binary-third-Q-commutes : (r : Resolution23Q) → binaryRefineQ (thirdRefineQ r) ≡ thirdRefineQ (binaryRefineQ r)
binary-third-Q-commutes (resolution23q a b q c) = refl
ternary-third-Q-commutes : (r : Resolution23Q) → ternaryRefineQ (thirdRefineQ r) ≡ thirdRefineQ (ternaryRefineQ r)
ternary-third-Q-commutes (resolution23q a b q c) = refl

resolution1 : Resolution23Q
resolution1 = resolution23q 0 0 5 0
resolution2 : Resolution23Q
resolution2 = resolution23q 1 0 5 0
resolution3 : Resolution23Q
resolution3 = resolution23q 0 1 5 0
resolution6 : Resolution23Q
resolution6 = resolution23q 1 1 5 0
resolution9 : Resolution23Q
resolution9 = resolution23q 0 2 5 0
resolution27 : Resolution23Q
resolution27 = resolution23q 0 3 5 0

resolution1-count : mixedSectorCount resolution1 ≡ 1
resolution1-count = refl
resolution2-count : mixedSectorCount resolution2 ≡ 2
resolution2-count = refl
resolution3-count : mixedSectorCount resolution3 ≡ 3
resolution3-count = refl
resolution6-count : mixedSectorCount resolution6 ≡ 6
resolution6-count = refl
resolution9-count : mixedSectorCount resolution9 ≡ 9
resolution9-count = refl
resolution27-count : mixedSectorCount resolution27 ≡ 27
resolution27-count = refl
resolution9-third-triadic-step : ternaryRefineQ resolution9 ≡ resolution27
resolution9-third-triadic-step = refl

record MixedPrimeResolutionBoundary : Set where
  constructor mkMixedPrimeResolutionBoundary
  field
    coordinateCarrier : Set
    interpretation : String
    arbitraryBaseIsPrimePromoted : Bool
    arbitraryBaseIsPrimePromotedIsFalse : arbitraryBaseIsPrimePromoted ≡ false
    chineseRemainderProductPromotedWithoutCoprimeWitness : Bool
    chineseRemainderProductPromotedWithoutCoprimeWitnessIsFalse : chineseRemainderProductPromotedWithoutCoprimeWitness ≡ false

mixedPrimeResolutionBoundary : MixedPrimeResolutionBoundary
mixedPrimeResolutionBoundary =
  mkMixedPrimeResolutionBoundary Resolution23Q
    "2^a 3^b q^c is a factor-depth coordinate; CRT decomposition requires explicit pairwise-coprime witnesses and q-primality is a separate gate"
    false refl false refl
