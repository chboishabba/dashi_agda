{-# OPTIONS --safe #-}
module DASHI.Cognition.CCDCOEP3G20RGMemberPanelExact where

-- Original empirical measurement ownership: G20 Research Group,
-- original report authors named in CCDCOEP3G20ComplianceObservedExact.
-- Values transcribed from each report's original web Table 2 (20 member
-- entries including EU). No raw-byte independent verification is claimed.
-- No fossil-subsidy quantity, emissions change or causal campaign effect.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List using (List; []; _∷_)

data Score : Set where
  minusOne : Score
  zeroScore : Score
  plusOne : Score

brisbaneFossilMembers : List Score
brisbaneFossilMembers =
  minusOne ∷ minusOne ∷ zeroScore ∷ minusOne ∷ minusOne ∷ plusOne ∷ minusOne ∷ zeroScore ∷ zeroScore ∷ minusOne ∷ minusOne ∷ zeroScore ∷ zeroScore ∷ minusOne ∷ minusOne ∷ minusOne ∷ minusOne ∷ zeroScore ∷ plusOne ∷ zeroScore ∷ []

antalyaFossilMembers : List Score
antalyaFossilMembers =
  plusOne ∷ minusOne ∷ minusOne ∷ zeroScore ∷ zeroScore ∷ zeroScore ∷ zeroScore ∷ plusOne ∷ minusOne ∷ zeroScore ∷ minusOne ∷ zeroScore ∷ minusOne ∷ minusOne ∷ zeroScore ∷ minusOne ∷ minusOne ∷ minusOne ∷ plusOne ∷ minusOne ∷ []

lengthScores : List Score → Nat
lengthScores [] = zero
lengthScores (_ ∷ xs) = suc (lengthScores xs)

minusCount : List Score → Nat
minusCount [] = zero
minusCount (minusOne ∷ xs) = suc (minusCount xs)
minusCount (_ ∷ xs) = minusCount xs

zeroCount : List Score → Nat
zeroCount [] = zero
zeroCount (zeroScore ∷ xs) = suc (zeroCount xs)
zeroCount (_ ∷ xs) = zeroCount xs

plusCount : List Score → Nat
plusCount [] = zero
plusCount (plusOne ∷ xs) = suc (plusCount xs)
plusCount (_ ∷ xs) = plusCount xs

brisbaneHasTwentyMembers : lengthScores brisbaneFossilMembers ≡ 20
brisbaneHasTwentyMembers = refl

antalyaHasTwentyMembers : lengthScores antalyaFossilMembers ≡ 20
antalyaHasTwentyMembers = refl

brisbaneMinusEleven : minusCount brisbaneFossilMembers ≡ 11
brisbaneMinusEleven = refl

brisbanePlusTwo : plusCount brisbaneFossilMembers ≡ 2
brisbanePlusTwo = refl

brisbaneZeroSeven : zeroCount brisbaneFossilMembers ≡ 7
brisbaneZeroSeven = refl

antalyaMinusTen : minusCount antalyaFossilMembers ≡ 10
antalyaMinusTen = refl

antalyaPlusThree : plusCount antalyaFossilMembers ≡ 3
antalyaPlusThree = refl

antalyaZeroSeven : zeroCount antalyaFossilMembers ≡ 7
antalyaZeroSeven = refl

-- Original member arithmetic: -11 + 2 = -9 (mean -0.45);
-- -10 + 3 = -7 (mean -0.35). Agda proves counts and nonnegative
-- arithmetic, not a replacement for original editorial table review.
brisbaneNineNetMinus :
  minusCount brisbaneFossilMembers
  ≡ plusCount brisbaneFossilMembers + 9
brisbaneNineNetMinus = refl

antalyaSevenNetMinus :
  minusCount antalyaFossilMembers
  ≡ plusCount antalyaFossilMembers + 7
antalyaSevenNetMinus = refl
