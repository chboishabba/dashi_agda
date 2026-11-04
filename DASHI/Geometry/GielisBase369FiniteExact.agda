module DASHI.Geometry.GielisBase369FiniteExact where

-- Gielis 2003 superformula; special case a=b=1, n1=2, n2=n3=4:
--   r_m(theta)^(-2) = (3 + cos(m theta))/4
-- On the 18-sector grid, twice the centered cosine is integral for
-- m in {3,6,9}. This module contains actual finite checkable equations;
-- the real-analytic identification is a separate gate, not silently assumed.
--
-- Reuse the established C18 carrier; do not redefine the Base369 tower.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (_+_)
open import Data.Integer using (ℤ; +_; -[1+_])
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)
open import Data.List.Base using (List; []; _∷_)
import DASHI.Foundations.Base369CirclePhase as Phase
open Phase using (Phase18; phase18-index; fromPhase18Index)


-- 2 cos(2 pi 3 j / 18), exactly on j = 0,...,17.
signal3 : Phase18 → ℤ
signal3 Phase.p18-0 = + 2
signal3 Phase.p18-1 = + 1
signal3 Phase.p18-2 = -[1+ 0 ]
signal3 Phase.p18-3 = -[1+ 1 ]
signal3 Phase.p18-4 = -[1+ 0 ]
signal3 Phase.p18-5 = + 1
signal3 Phase.p18-6 = + 2
signal3 Phase.p18-7 = + 1
signal3 Phase.p18-8 = -[1+ 0 ]
signal3 Phase.p18-9 = -[1+ 1 ]
signal3 Phase.p18-10 = -[1+ 0 ]
signal3 Phase.p18-11 = + 1
signal3 Phase.p18-12 = + 2
signal3 Phase.p18-13 = + 1
signal3 Phase.p18-14 = -[1+ 0 ]
signal3 Phase.p18-15 = -[1+ 1 ]
signal3 Phase.p18-16 = -[1+ 0 ]
signal3 Phase.p18-17 = + 1

-- 2 cos(2 pi 6 j / 18), exactly on j = 0,...,17.
signal6 : Phase18 → ℤ
signal6 Phase.p18-0 = + 2
signal6 Phase.p18-1 = -[1+ 0 ]
signal6 Phase.p18-2 = -[1+ 0 ]
signal6 Phase.p18-3 = + 2
signal6 Phase.p18-4 = -[1+ 0 ]
signal6 Phase.p18-5 = -[1+ 0 ]
signal6 Phase.p18-6 = + 2
signal6 Phase.p18-7 = -[1+ 0 ]
signal6 Phase.p18-8 = -[1+ 0 ]
signal6 Phase.p18-9 = + 2
signal6 Phase.p18-10 = -[1+ 0 ]
signal6 Phase.p18-11 = -[1+ 0 ]
signal6 Phase.p18-12 = + 2
signal6 Phase.p18-13 = -[1+ 0 ]
signal6 Phase.p18-14 = -[1+ 0 ]
signal6 Phase.p18-15 = + 2
signal6 Phase.p18-16 = -[1+ 0 ]
signal6 Phase.p18-17 = -[1+ 0 ]

-- 2 cos(2 pi 9 j / 18), exactly on j = 0,...,17.
signal9 : Phase18 → ℤ
signal9 Phase.p18-0 = + 2
signal9 Phase.p18-1 = -[1+ 1 ]
signal9 Phase.p18-2 = + 2
signal9 Phase.p18-3 = -[1+ 1 ]
signal9 Phase.p18-4 = + 2
signal9 Phase.p18-5 = -[1+ 1 ]
signal9 Phase.p18-6 = + 2
signal9 Phase.p18-7 = -[1+ 1 ]
signal9 Phase.p18-8 = + 2
signal9 Phase.p18-9 = -[1+ 1 ]
signal9 Phase.p18-10 = + 2
signal9 Phase.p18-11 = -[1+ 1 ]
signal9 Phase.p18-12 = + 2
signal9 Phase.p18-13 = -[1+ 1 ]
signal9 Phase.p18-14 = + 2
signal9 Phase.p18-15 = -[1+ 1 ]
signal9 Phase.p18-16 = + 2
signal9 Phase.p18-17 = -[1+ 1 ]

-- Rotations of 2 pi / m correspond to shifts of 18/m sectors.
rotate3 : Phase18 → Phase18
rotate3 p = fromPhase18Index (phase18-index p + 6)

rotate6 : Phase18 → Phase18
rotate6 p = fromPhase18Index (phase18-index p + 3)

rotate9 : Phase18 → Phase18
rotate9 p = fromPhase18Index (phase18-index p + 2)

reflect18 : Phase18 → Phase18
reflect18 Phase.p18-0 = Phase.p18-0
reflect18 Phase.p18-1 = Phase.p18-17
reflect18 Phase.p18-2 = Phase.p18-16
reflect18 Phase.p18-3 = Phase.p18-15
reflect18 Phase.p18-4 = Phase.p18-14
reflect18 Phase.p18-5 = Phase.p18-13
reflect18 Phase.p18-6 = Phase.p18-12
reflect18 Phase.p18-7 = Phase.p18-11
reflect18 Phase.p18-8 = Phase.p18-10
reflect18 Phase.p18-9 = Phase.p18-9
reflect18 Phase.p18-10 = Phase.p18-8
reflect18 Phase.p18-11 = Phase.p18-7
reflect18 Phase.p18-12 = Phase.p18-6
reflect18 Phase.p18-13 = Phase.p18-5
reflect18 Phase.p18-14 = Phase.p18-4
reflect18 Phase.p18-15 = Phase.p18-3
reflect18 Phase.p18-16 = Phase.p18-2
reflect18 Phase.p18-17 = Phase.p18-1

rotation3PreservesSignal : (p : Phase18) → signal3 (rotate3 p) ≡ signal3 p
rotation3PreservesSignal Phase.p18-0 = refl
rotation3PreservesSignal Phase.p18-1 = refl
rotation3PreservesSignal Phase.p18-2 = refl
rotation3PreservesSignal Phase.p18-3 = refl
rotation3PreservesSignal Phase.p18-4 = refl
rotation3PreservesSignal Phase.p18-5 = refl
rotation3PreservesSignal Phase.p18-6 = refl
rotation3PreservesSignal Phase.p18-7 = refl
rotation3PreservesSignal Phase.p18-8 = refl
rotation3PreservesSignal Phase.p18-9 = refl
rotation3PreservesSignal Phase.p18-10 = refl
rotation3PreservesSignal Phase.p18-11 = refl
rotation3PreservesSignal Phase.p18-12 = refl
rotation3PreservesSignal Phase.p18-13 = refl
rotation3PreservesSignal Phase.p18-14 = refl
rotation3PreservesSignal Phase.p18-15 = refl
rotation3PreservesSignal Phase.p18-16 = refl
rotation3PreservesSignal Phase.p18-17 = refl
reflection3PreservesSignal : (p : Phase18) → signal3 (reflect18 p) ≡ signal3 p
reflection3PreservesSignal Phase.p18-0 = refl
reflection3PreservesSignal Phase.p18-1 = refl
reflection3PreservesSignal Phase.p18-2 = refl
reflection3PreservesSignal Phase.p18-3 = refl
reflection3PreservesSignal Phase.p18-4 = refl
reflection3PreservesSignal Phase.p18-5 = refl
reflection3PreservesSignal Phase.p18-6 = refl
reflection3PreservesSignal Phase.p18-7 = refl
reflection3PreservesSignal Phase.p18-8 = refl
reflection3PreservesSignal Phase.p18-9 = refl
reflection3PreservesSignal Phase.p18-10 = refl
reflection3PreservesSignal Phase.p18-11 = refl
reflection3PreservesSignal Phase.p18-12 = refl
reflection3PreservesSignal Phase.p18-13 = refl
reflection3PreservesSignal Phase.p18-14 = refl
reflection3PreservesSignal Phase.p18-15 = refl
reflection3PreservesSignal Phase.p18-16 = refl
reflection3PreservesSignal Phase.p18-17 = refl

rotation6PreservesSignal : (p : Phase18) → signal6 (rotate6 p) ≡ signal6 p
rotation6PreservesSignal Phase.p18-0 = refl
rotation6PreservesSignal Phase.p18-1 = refl
rotation6PreservesSignal Phase.p18-2 = refl
rotation6PreservesSignal Phase.p18-3 = refl
rotation6PreservesSignal Phase.p18-4 = refl
rotation6PreservesSignal Phase.p18-5 = refl
rotation6PreservesSignal Phase.p18-6 = refl
rotation6PreservesSignal Phase.p18-7 = refl
rotation6PreservesSignal Phase.p18-8 = refl
rotation6PreservesSignal Phase.p18-9 = refl
rotation6PreservesSignal Phase.p18-10 = refl
rotation6PreservesSignal Phase.p18-11 = refl
rotation6PreservesSignal Phase.p18-12 = refl
rotation6PreservesSignal Phase.p18-13 = refl
rotation6PreservesSignal Phase.p18-14 = refl
rotation6PreservesSignal Phase.p18-15 = refl
rotation6PreservesSignal Phase.p18-16 = refl
rotation6PreservesSignal Phase.p18-17 = refl
reflection6PreservesSignal : (p : Phase18) → signal6 (reflect18 p) ≡ signal6 p
reflection6PreservesSignal Phase.p18-0 = refl
reflection6PreservesSignal Phase.p18-1 = refl
reflection6PreservesSignal Phase.p18-2 = refl
reflection6PreservesSignal Phase.p18-3 = refl
reflection6PreservesSignal Phase.p18-4 = refl
reflection6PreservesSignal Phase.p18-5 = refl
reflection6PreservesSignal Phase.p18-6 = refl
reflection6PreservesSignal Phase.p18-7 = refl
reflection6PreservesSignal Phase.p18-8 = refl
reflection6PreservesSignal Phase.p18-9 = refl
reflection6PreservesSignal Phase.p18-10 = refl
reflection6PreservesSignal Phase.p18-11 = refl
reflection6PreservesSignal Phase.p18-12 = refl
reflection6PreservesSignal Phase.p18-13 = refl
reflection6PreservesSignal Phase.p18-14 = refl
reflection6PreservesSignal Phase.p18-15 = refl
reflection6PreservesSignal Phase.p18-16 = refl
reflection6PreservesSignal Phase.p18-17 = refl

rotation9PreservesSignal : (p : Phase18) → signal9 (rotate9 p) ≡ signal9 p
rotation9PreservesSignal Phase.p18-0 = refl
rotation9PreservesSignal Phase.p18-1 = refl
rotation9PreservesSignal Phase.p18-2 = refl
rotation9PreservesSignal Phase.p18-3 = refl
rotation9PreservesSignal Phase.p18-4 = refl
rotation9PreservesSignal Phase.p18-5 = refl
rotation9PreservesSignal Phase.p18-6 = refl
rotation9PreservesSignal Phase.p18-7 = refl
rotation9PreservesSignal Phase.p18-8 = refl
rotation9PreservesSignal Phase.p18-9 = refl
rotation9PreservesSignal Phase.p18-10 = refl
rotation9PreservesSignal Phase.p18-11 = refl
rotation9PreservesSignal Phase.p18-12 = refl
rotation9PreservesSignal Phase.p18-13 = refl
rotation9PreservesSignal Phase.p18-14 = refl
rotation9PreservesSignal Phase.p18-15 = refl
rotation9PreservesSignal Phase.p18-16 = refl
rotation9PreservesSignal Phase.p18-17 = refl
reflection9PreservesSignal : (p : Phase18) → signal9 (reflect18 p) ≡ signal9 p
reflection9PreservesSignal Phase.p18-0 = refl
reflection9PreservesSignal Phase.p18-1 = refl
reflection9PreservesSignal Phase.p18-2 = refl
reflection9PreservesSignal Phase.p18-3 = refl
reflection9PreservesSignal Phase.p18-4 = refl
reflection9PreservesSignal Phase.p18-5 = refl
reflection9PreservesSignal Phase.p18-6 = refl
reflection9PreservesSignal Phase.p18-7 = refl
reflection9PreservesSignal Phase.p18-8 = refl
reflection9PreservesSignal Phase.p18-9 = refl
reflection9PreservesSignal Phase.p18-10 = refl
reflection9PreservesSignal Phase.p18-11 = refl
reflection9PreservesSignal Phase.p18-12 = refl
reflection9PreservesSignal Phase.p18-13 = refl
reflection9PreservesSignal Phase.p18-14 = refl
reflection9PreservesSignal Phase.p18-15 = refl
reflection9PreservesSignal Phase.p18-16 = refl
reflection9PreservesSignal Phase.p18-17 = refl

reflectionInvolutive : (p : Phase18) → reflect18 (reflect18 p) ≡ p
reflectionInvolutive Phase.p18-0 = refl
reflectionInvolutive Phase.p18-1 = refl
reflectionInvolutive Phase.p18-2 = refl
reflectionInvolutive Phase.p18-3 = refl
reflectionInvolutive Phase.p18-4 = refl
reflectionInvolutive Phase.p18-5 = refl
reflectionInvolutive Phase.p18-6 = refl
reflectionInvolutive Phase.p18-7 = refl
reflectionInvolutive Phase.p18-8 = refl
reflectionInvolutive Phase.p18-9 = refl
reflectionInvolutive Phase.p18-10 = refl
reflectionInvolutive Phase.p18-11 = refl
reflectionInvolutive Phase.p18-12 = refl
reflectionInvolutive Phase.p18-13 = refl
reflectionInvolutive Phase.p18-14 = refl
reflectionInvolutive Phase.p18-15 = refl
reflectionInvolutive Phase.p18-16 = refl
reflectionInvolutive Phase.p18-17 = refl

rotation3Order : (p : Phase18) → rotate3 (rotate3 (rotate3 (p))) ≡ p
rotation3Order Phase.p18-0 = refl
rotation3Order Phase.p18-1 = refl
rotation3Order Phase.p18-2 = refl
rotation3Order Phase.p18-3 = refl
rotation3Order Phase.p18-4 = refl
rotation3Order Phase.p18-5 = refl
rotation3Order Phase.p18-6 = refl
rotation3Order Phase.p18-7 = refl
rotation3Order Phase.p18-8 = refl
rotation3Order Phase.p18-9 = refl
rotation3Order Phase.p18-10 = refl
rotation3Order Phase.p18-11 = refl
rotation3Order Phase.p18-12 = refl
rotation3Order Phase.p18-13 = refl
rotation3Order Phase.p18-14 = refl
rotation3Order Phase.p18-15 = refl
rotation3Order Phase.p18-16 = refl
rotation3Order Phase.p18-17 = refl

rotation6Order : (p : Phase18) → rotate6 (rotate6 (rotate6 (rotate6 (rotate6 (rotate6 (p)))))) ≡ p
rotation6Order Phase.p18-0 = refl
rotation6Order Phase.p18-1 = refl
rotation6Order Phase.p18-2 = refl
rotation6Order Phase.p18-3 = refl
rotation6Order Phase.p18-4 = refl
rotation6Order Phase.p18-5 = refl
rotation6Order Phase.p18-6 = refl
rotation6Order Phase.p18-7 = refl
rotation6Order Phase.p18-8 = refl
rotation6Order Phase.p18-9 = refl
rotation6Order Phase.p18-10 = refl
rotation6Order Phase.p18-11 = refl
rotation6Order Phase.p18-12 = refl
rotation6Order Phase.p18-13 = refl
rotation6Order Phase.p18-14 = refl
rotation6Order Phase.p18-15 = refl
rotation6Order Phase.p18-16 = refl
rotation6Order Phase.p18-17 = refl

rotation9Order : (p : Phase18) → rotate9 (rotate9 (rotate9 (rotate9 (rotate9 (rotate9 (rotate9 (rotate9 (rotate9 (p))))))))) ≡ p
rotation9Order Phase.p18-0 = refl
rotation9Order Phase.p18-1 = refl
rotation9Order Phase.p18-2 = refl
rotation9Order Phase.p18-3 = refl
rotation9Order Phase.p18-4 = refl
rotation9Order Phase.p18-5 = refl
rotation9Order Phase.p18-6 = refl
rotation9Order Phase.p18-7 = refl
rotation9Order Phase.p18-8 = refl
rotation9Order Phase.p18-9 = refl
rotation9Order Phase.p18-10 = refl
rotation9Order Phase.p18-11 = refl
rotation9Order Phase.p18-12 = refl
rotation9Order Phase.p18-13 = refl
rotation9Order Phase.p18-14 = refl
rotation9Order Phase.p18-15 = refl
rotation9Order Phase.p18-16 = refl
rotation9Order Phase.p18-17 = refl

-- Exact integer Gram matrix of the three 18-sector signatures.
-- Each signal has been scaled by 2; the Gram diagonal is 36,36,72.

sample : (Phase18 → ℤ) → List ℤ
sample f =

  f Phase.p18-0 ∷
  f Phase.p18-1 ∷
  f Phase.p18-2 ∷
  f Phase.p18-3 ∷
  f Phase.p18-4 ∷
  f Phase.p18-5 ∷
  f Phase.p18-6 ∷
  f Phase.p18-7 ∷
  f Phase.p18-8 ∷
  f Phase.p18-9 ∷
  f Phase.p18-10 ∷
  f Phase.p18-11 ∷
  f Phase.p18-12 ∷
  f Phase.p18-13 ∷
  f Phase.p18-14 ∷
  f Phase.p18-15 ∷
  f Phase.p18-16 ∷
  f Phase.p18-17 ∷
  []

dot : List ℤ → List ℤ → ℤ
dot (x ∷ xs) (y ∷ ys) = (x *ℤ y) +ℤ dot xs ys
dot _ _ = + 0

gram33 : dot (sample signal3) (sample signal3) ≡ + 36
gram33 = refl

gram66 : dot (sample signal6) (sample signal6) ≡ + 36
gram66 = refl

gram99 : dot (sample signal9) (sample signal9) ≡ + 72
gram99 = refl

gram36 : dot (sample signal3) (sample signal6) ≡ + 0
gram36 = refl

gram39 : dot (sample signal3) (sample signal9) ≡ + 0
gram39 = refl

gram69 : dot (sample signal6) (sample signal9) ≡ + 0
gram69 = refl

-- Finite mode orthogonality is kernel-checkable after Agda invocation.
-- Not claimed: continuous analytic Gielis equality, complex Fourier
-- reconstruction, eigenvalue convergence, or a physical optical theorem.
