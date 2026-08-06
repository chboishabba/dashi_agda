module DASHI.Biology.TriadicKernelLiftQuotientExact where

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)

------------------------------------------------------------------------
-- Exact finite kernel algebra for the round-four reasoning-field tranche.
--
-- A nine-sheet is not an unexplained map K_d -> K_(d+2).  It is exactly a
-- pair of triadic coordinates, so K_(d+2) is product-equivalent to K_d x T^2.
-- The module also separates the coordinatewise support/orientation fold from
-- the global inversion quotient and gives the literal five-orbit quotient of
-- one nine-state sheet.

data KernelTrit : Set where
  negativeTrit : KernelTrit
  zeroTrit : KernelTrit
  positiveTrit : KernelTrit

negateTrit : KernelTrit → KernelTrit
negateTrit negativeTrit = positiveTrit
negateTrit zeroTrit = zeroTrit
negateTrit positiveTrit = negativeTrit

negateTritInvolutive : (x : KernelTrit) → negateTrit (negateTrit x) ≡ x
negateTritInvolutive negativeTrit = refl
negateTritInvolutive zeroTrit = refl
negateTritInvolutive positiveTrit = refl

Kernel : Nat → Set
Kernel d = Vec KernelTrit d

NineSheet : Set
NineSheet = KernelTrit × KernelTrit

liftNine : ∀ {d : Nat} → Kernel d → NineSheet → Kernel (suc (suc d))
liftNine xs sheet = proj₁ sheet vcons proj₂ sheet vcons xs

splitNine : ∀ {d : Nat} → Kernel (suc (suc d)) → Kernel d × NineSheet
splitNine (a vcons b vcons xs) = xs , (a , b)

splitLiftNine :
  ∀ {d : Nat} (xs : Kernel d) (sheet : NineSheet) →
  splitNine (liftNine xs sheet) ≡ (xs , sheet)
splitLiftNine xs (a , b) = refl

liftSplitNine :
  ∀ {d : Nat} (xs : Kernel (suc (suc d))) →
  liftNine (proj₁ (splitNine xs)) (proj₂ (splitNine xs)) ≡ xs
liftSplitNine (a vcons b vcons xs) = refl

------------------------------------------------------------------------
-- Coordinatewise support/orientation fold.  The inactive state carries no
-- spurious sign, so the folded carrier has exactly three constructors.

data TritOrientation : Set where
  negativeOrientation : TritOrientation
  positiveOrientation : TritOrientation

data FoldedTrit : Set where
  inactiveTrit : FoldedTrit
  activeTrit : TritOrientation → FoldedTrit

foldTrit : KernelTrit → FoldedTrit
foldTrit negativeTrit = activeTrit negativeOrientation
foldTrit zeroTrit = inactiveTrit
foldTrit positiveTrit = activeTrit positiveOrientation

unfoldTrit : FoldedTrit → KernelTrit
unfoldTrit inactiveTrit = zeroTrit
unfoldTrit (activeTrit negativeOrientation) = negativeTrit
unfoldTrit (activeTrit positiveOrientation) = positiveTrit

unfoldFoldTrit : (x : KernelTrit) → unfoldTrit (foldTrit x) ≡ x
unfoldFoldTrit negativeTrit = refl
unfoldFoldTrit zeroTrit = refl
unfoldFoldTrit positiveTrit = refl

foldUnfoldTrit : (x : FoldedTrit) → foldTrit (unfoldTrit x) ≡ x
foldUnfoldTrit inactiveTrit = refl
foldUnfoldTrit (activeTrit negativeOrientation) = refl
foldUnfoldTrit (activeTrit positiveOrientation) = refl

------------------------------------------------------------------------
-- Global inversion quotient of one nine-state sheet.
--
-- The five constructors are the zero orbit, the two coordinate-axis orbits,
-- the equal-sign diagonal orbit, and the opposite-sign diagonal orbit.

data NineOrbit : Set where
  zeroOrbit : NineOrbit
  firstAxisOrbit : NineOrbit
  secondAxisOrbit : NineOrbit
  equalSignOrbit : NineOrbit
  oppositeSignOrbit : NineOrbit

negateNine : NineSheet → NineSheet
negateNine (a , b) = negateTrit a , negateTrit b

quotientNine : NineSheet → NineOrbit
quotientNine (zeroTrit , zeroTrit) = zeroOrbit
quotientNine (negativeTrit , zeroTrit) = firstAxisOrbit
quotientNine (positiveTrit , zeroTrit) = firstAxisOrbit
quotientNine (zeroTrit , negativeTrit) = secondAxisOrbit
quotientNine (zeroTrit , positiveTrit) = secondAxisOrbit
quotientNine (negativeTrit , negativeTrit) = equalSignOrbit
quotientNine (positiveTrit , positiveTrit) = equalSignOrbit
quotientNine (negativeTrit , positiveTrit) = oppositeSignOrbit
quotientNine (positiveTrit , negativeTrit) = oppositeSignOrbit

quotientNineNegationInvariant :
  (x : NineSheet) → quotientNine (negateNine x) ≡ quotientNine x
quotientNineNegationInvariant (zeroTrit , zeroTrit) = refl
quotientNineNegationInvariant (negativeTrit , zeroTrit) = refl
quotientNineNegationInvariant (positiveTrit , zeroTrit) = refl
quotientNineNegationInvariant (zeroTrit , negativeTrit) = refl
quotientNineNegationInvariant (zeroTrit , positiveTrit) = refl
quotientNineNegationInvariant (negativeTrit , negativeTrit) = refl
quotientNineNegationInvariant (positiveTrit , positiveTrit) = refl
quotientNineNegationInvariant (negativeTrit , positiveTrit) = refl
quotientNineNegationInvariant (positiveTrit , negativeTrit) = refl

canonicalNineRepresentative : NineOrbit → NineSheet
canonicalNineRepresentative zeroOrbit = zeroTrit , zeroTrit
canonicalNineRepresentative firstAxisOrbit = positiveTrit , zeroTrit
canonicalNineRepresentative secondAxisOrbit = zeroTrit , positiveTrit
canonicalNineRepresentative equalSignOrbit = positiveTrit , positiveTrit
canonicalNineRepresentative oppositeSignOrbit = positiveTrit , negativeTrit

canonicalRepresentativeReturnsOrbit :
  (o : NineOrbit) → quotientNine (canonicalNineRepresentative o) ≡ o
canonicalRepresentativeReturnsOrbit zeroOrbit = refl
canonicalRepresentativeReturnsOrbit firstAxisOrbit = refl
canonicalRepresentativeReturnsOrbit secondAxisOrbit = refl
canonicalRepresentativeReturnsOrbit equalSignOrbit = refl
canonicalRepresentativeReturnsOrbit oppositeSignOrbit = refl

------------------------------------------------------------------------
-- Type-level endofunction tower.  This is the exact recursion F_(n+1)=F_n^F_n
-- and is deliberately kept distinct from literal fixed-base tetration.

RuleLevel : Nat → Set
RuleLevel zero = NineSheet
RuleLevel (suc n) = RuleLevel n → RuleLevel n

identityRule : (n : Nat) → RuleLevel (suc n)
identityRule n x = x

identityRuleActs :
  (n : Nat) (x : RuleLevel n) → identityRule n x ≡ x
identityRuleActs n x = refl

record TriadicKernelLiftBoundary : Set where
  constructor triadicKernelLiftBoundary
  field
    nineLiftAddsOneContinuousFieldComponent : Bool
    nineLiftAddsOneContinuousFieldComponentIsFalse :
      nineLiftAddsOneContinuousFieldComponent ≡ false

    coordinateFoldEqualsGlobalOrbitQuotient : Bool
    coordinateFoldEqualsGlobalOrbitQuotientIsFalse :
      coordinateFoldEqualsGlobalOrbitQuotient ≡ false

    endofunctionTowerIsLiteralBaseNineTetration : Bool
    endofunctionTowerIsLiteralBaseNineTetrationIsFalse :
      endofunctionTowerIsLiteralBaseNineTetration ≡ false

open TriadicKernelLiftBoundary public

canonicalTriadicKernelLiftBoundary : TriadicKernelLiftBoundary
canonicalTriadicKernelLiftBoundary =
  triadicKernelLiftBoundary false refl false refl false refl
