module DASHI.Geometry.GielisBase369NyquistPhase36Exact where

-- Minimal exact Nyquist/orientation witness for selected Gielis m=9.
-- For theta_j = 2*pi*j/36, cos(9*theta_j) is 1,0,-1,0;
-- sin(9*theta_j) is 0,1,0,-1;
-- sin(27*theta_j) is 0,-1,0,1.
-- On the coarser 18-sample grid, both sine modes vanish identically.
-- These are finite integer tables; no classical Shannon theorem or
-- ordinary-real sine implementation is inferred without further proof.
-- The existing C18 carrier is reused, not redefined.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Empty using (⊥)

import DASHI.Foundations.Base369CirclePhase as Phase
import DASHI.Geometry.GielisBase369FiniteExact as Gielis

data Phase36 : Set where
  p36-0 p36-1 p36-2 p36-3 p36-4 p36-5 : Phase36
  p36-6 p36-7 p36-8 p36-9 p36-10 p36-11 : Phase36
  p36-12 p36-13 p36-14 p36-15 p36-16 p36-17 : Phase36
  p36-18 p36-19 p36-20 p36-21 p36-22 p36-23 : Phase36
  p36-24 p36-25 p36-26 p36-27 p36-28 p36-29 : Phase36
  p36-30 p36-31 p36-32 p36-33 p36-34 p36-35 : Phase36

-- Every coarse sector is embedded at the corresponding even fine sample.
even18To36 : Phase.Phase18 → Phase36
even18To36 Phase.p18-0 = p36-0
even18To36 Phase.p18-1 = p36-2
even18To36 Phase.p18-2 = p36-4
even18To36 Phase.p18-3 = p36-6
even18To36 Phase.p18-4 = p36-8
even18To36 Phase.p18-5 = p36-10
even18To36 Phase.p18-6 = p36-12
even18To36 Phase.p18-7 = p36-14
even18To36 Phase.p18-8 = p36-16
even18To36 Phase.p18-9 = p36-18
even18To36 Phase.p18-10 = p36-20
even18To36 Phase.p18-11 = p36-22
even18To36 Phase.p18-12 = p36-24
even18To36 Phase.p18-13 = p36-26
even18To36 Phase.p18-14 = p36-28
even18To36 Phase.p18-15 = p36-30
even18To36 Phase.p18-16 = p36-32
even18To36 Phase.p18-17 = p36-34

cosNine : Phase36 → ℤ
cosNine p36-0 = + 1
cosNine p36-1 = + 0
cosNine p36-2 = -[1+ 0 ]
cosNine p36-3 = + 0
cosNine p36-4 = + 1
cosNine p36-5 = + 0
cosNine p36-6 = -[1+ 0 ]
cosNine p36-7 = + 0
cosNine p36-8 = + 1
cosNine p36-9 = + 0
cosNine p36-10 = -[1+ 0 ]
cosNine p36-11 = + 0
cosNine p36-12 = + 1
cosNine p36-13 = + 0
cosNine p36-14 = -[1+ 0 ]
cosNine p36-15 = + 0
cosNine p36-16 = + 1
cosNine p36-17 = + 0
cosNine p36-18 = -[1+ 0 ]
cosNine p36-19 = + 0
cosNine p36-20 = + 1
cosNine p36-21 = + 0
cosNine p36-22 = -[1+ 0 ]
cosNine p36-23 = + 0
cosNine p36-24 = + 1
cosNine p36-25 = + 0
cosNine p36-26 = -[1+ 0 ]
cosNine p36-27 = + 0
cosNine p36-28 = + 1
cosNine p36-29 = + 0
cosNine p36-30 = -[1+ 0 ]
cosNine p36-31 = + 0
cosNine p36-32 = + 1
cosNine p36-33 = + 0
cosNine p36-34 = -[1+ 0 ]
cosNine p36-35 = + 0

sinNine : Phase36 → ℤ
sinNine p36-0 = + 0
sinNine p36-1 = + 1
sinNine p36-2 = + 0
sinNine p36-3 = -[1+ 0 ]
sinNine p36-4 = + 0
sinNine p36-5 = + 1
sinNine p36-6 = + 0
sinNine p36-7 = -[1+ 0 ]
sinNine p36-8 = + 0
sinNine p36-9 = + 1
sinNine p36-10 = + 0
sinNine p36-11 = -[1+ 0 ]
sinNine p36-12 = + 0
sinNine p36-13 = + 1
sinNine p36-14 = + 0
sinNine p36-15 = -[1+ 0 ]
sinNine p36-16 = + 0
sinNine p36-17 = + 1
sinNine p36-18 = + 0
sinNine p36-19 = -[1+ 0 ]
sinNine p36-20 = + 0
sinNine p36-21 = + 1
sinNine p36-22 = + 0
sinNine p36-23 = -[1+ 0 ]
sinNine p36-24 = + 0
sinNine p36-25 = + 1
sinNine p36-26 = + 0
sinNine p36-27 = -[1+ 0 ]
sinNine p36-28 = + 0
sinNine p36-29 = + 1
sinNine p36-30 = + 0
sinNine p36-31 = -[1+ 0 ]
sinNine p36-32 = + 0
sinNine p36-33 = + 1
sinNine p36-34 = + 0
sinNine p36-35 = -[1+ 0 ]

sinTwentySeven : Phase36 → ℤ
sinTwentySeven p36-0 = + 0
sinTwentySeven p36-1 = -[1+ 0 ]
sinTwentySeven p36-2 = + 0
sinTwentySeven p36-3 = + 1
sinTwentySeven p36-4 = + 0
sinTwentySeven p36-5 = -[1+ 0 ]
sinTwentySeven p36-6 = + 0
sinTwentySeven p36-7 = + 1
sinTwentySeven p36-8 = + 0
sinTwentySeven p36-9 = -[1+ 0 ]
sinTwentySeven p36-10 = + 0
sinTwentySeven p36-11 = + 1
sinTwentySeven p36-12 = + 0
sinTwentySeven p36-13 = -[1+ 0 ]
sinTwentySeven p36-14 = + 0
sinTwentySeven p36-15 = + 1
sinTwentySeven p36-16 = + 0
sinTwentySeven p36-17 = -[1+ 0 ]
sinTwentySeven p36-18 = + 0
sinTwentySeven p36-19 = + 1
sinTwentySeven p36-20 = + 0
sinTwentySeven p36-21 = -[1+ 0 ]
sinTwentySeven p36-22 = + 0
sinTwentySeven p36-23 = + 1
sinTwentySeven p36-24 = + 0
sinTwentySeven p36-25 = -[1+ 0 ]
sinTwentySeven p36-26 = + 0
sinTwentySeven p36-27 = + 1
sinTwentySeven p36-28 = + 0
sinTwentySeven p36-29 = -[1+ 0 ]
sinTwentySeven p36-30 = + 0
sinTwentySeven p36-31 = + 1
sinTwentySeven p36-32 = + 0
sinTwentySeven p36-33 = -[1+ 0 ]
sinTwentySeven p36-34 = + 0
sinTwentySeven p36-35 = + 1

-- A strict 18-point sampling has a real loss: both oriented sine modes
-- have exactly the same coarse observations (all zero).
sinNineVanishesOnEvenSamples :
  (p : Phase.Phase18) → sinNine (even18To36 p) ≡ + 0
sinNineVanishesOnEvenSamples Phase.p18-0 = refl
sinNineVanishesOnEvenSamples Phase.p18-1 = refl
sinNineVanishesOnEvenSamples Phase.p18-2 = refl
sinNineVanishesOnEvenSamples Phase.p18-3 = refl
sinNineVanishesOnEvenSamples Phase.p18-4 = refl
sinNineVanishesOnEvenSamples Phase.p18-5 = refl
sinNineVanishesOnEvenSamples Phase.p18-6 = refl
sinNineVanishesOnEvenSamples Phase.p18-7 = refl
sinNineVanishesOnEvenSamples Phase.p18-8 = refl
sinNineVanishesOnEvenSamples Phase.p18-9 = refl
sinNineVanishesOnEvenSamples Phase.p18-10 = refl
sinNineVanishesOnEvenSamples Phase.p18-11 = refl
sinNineVanishesOnEvenSamples Phase.p18-12 = refl
sinNineVanishesOnEvenSamples Phase.p18-13 = refl
sinNineVanishesOnEvenSamples Phase.p18-14 = refl
sinNineVanishesOnEvenSamples Phase.p18-15 = refl
sinNineVanishesOnEvenSamples Phase.p18-16 = refl
sinNineVanishesOnEvenSamples Phase.p18-17 = refl

sinTwentySevenVanishesOnEvenSamples :
  (p : Phase.Phase18) → sinTwentySeven (even18To36 p) ≡ + 0
sinTwentySevenVanishesOnEvenSamples Phase.p18-0 = refl
sinTwentySevenVanishesOnEvenSamples Phase.p18-1 = refl
sinTwentySevenVanishesOnEvenSamples Phase.p18-2 = refl
sinTwentySevenVanishesOnEvenSamples Phase.p18-3 = refl
sinTwentySevenVanishesOnEvenSamples Phase.p18-4 = refl
sinTwentySevenVanishesOnEvenSamples Phase.p18-5 = refl
sinTwentySevenVanishesOnEvenSamples Phase.p18-6 = refl
sinTwentySevenVanishesOnEvenSamples Phase.p18-7 = refl
sinTwentySevenVanishesOnEvenSamples Phase.p18-8 = refl
sinTwentySevenVanishesOnEvenSamples Phase.p18-9 = refl
sinTwentySevenVanishesOnEvenSamples Phase.p18-10 = refl
sinTwentySevenVanishesOnEvenSamples Phase.p18-11 = refl
sinTwentySevenVanishesOnEvenSamples Phase.p18-12 = refl
sinTwentySevenVanishesOnEvenSamples Phase.p18-13 = refl
sinTwentySevenVanishesOnEvenSamples Phase.p18-14 = refl
sinTwentySevenVanishesOnEvenSamples Phase.p18-15 = refl
sinTwentySevenVanishesOnEvenSamples Phase.p18-16 = refl
sinTwentySevenVanishesOnEvenSamples Phase.p18-17 = refl

coarseSineAgreement :
  (p : Phase.Phase18) →
  sinNine (even18To36 p) ≡ sinTwentySeven (even18To36 p)
coarseSineAgreement Phase.p18-0 = refl
coarseSineAgreement Phase.p18-1 = refl
coarseSineAgreement Phase.p18-2 = refl
coarseSineAgreement Phase.p18-3 = refl
coarseSineAgreement Phase.p18-4 = refl
coarseSineAgreement Phase.p18-5 = refl
coarseSineAgreement Phase.p18-6 = refl
coarseSineAgreement Phase.p18-7 = refl
coarseSineAgreement Phase.p18-8 = refl
coarseSineAgreement Phase.p18-9 = refl
coarseSineAgreement Phase.p18-10 = refl
coarseSineAgreement Phase.p18-11 = refl
coarseSineAgreement Phase.p18-12 = refl
coarseSineAgreement Phase.p18-13 = refl
coarseSineAgreement Phase.p18-14 = refl
coarseSineAgreement Phase.p18-15 = refl
coarseSineAgreement Phase.p18-16 = refl
coarseSineAgreement Phase.p18-17 = refl

-- The 36-point odd sample distinguishes 9 from its folded 27-mode.
fineNineAtOne : sinNine p36-1 ≡ + 1
fineNineAtOne = refl

fineTwentySevenAtOne : sinTwentySeven p36-1 ≡ -[1+ 0 ]
fineTwentySevenAtOne = refl

fineModesDistinctAtOne :
  sinNine p36-1 ≡ sinTwentySeven p36-1 → ⊥
fineModesDistinctAtOne ()

-- Existing Gielis finite rotation theorem is reused by reference.
gielisC9RotationRetained :
  (p : Phase.Phase18) →
  Gielis.signal9 (Gielis.rotate9 p) ≡ Gielis.signal9 p
gielisC9RotationRetained = Gielis.rotation9PreservesSignal

-- These are exact finite interpolation facts. A genuine sampling theorem
-- needs a declared bandlimited function space, reconstruction map, and norm.
