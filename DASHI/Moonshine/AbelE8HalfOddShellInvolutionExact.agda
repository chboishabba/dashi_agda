module DASHI.Moonshine.AbelE8HalfOddShellInvolutionExact where

------------------------------------------------------------------------
-- UNBOUNDED E8 HALF-COORDINATE INVOLUTION FOR EVERY SHELL
--
-- A doubled half-integer coordinate is +/- (2m+1), m:Nat.
-- The signed magnitude squared does not depend on the sign.
-- For an even number of odd coordinates, sum(d_i) mod 4 is 0 or 2;
-- the distinguishing bit is XOR_i ((m_i mod 2) XOR negative_i).
--
-- Sign reversal of the first coordinate therefore preserves squared
-- norm and toggles that bit. This construction is valid for arbitrary
-- magnitudes m (not just the +/-1 root coordinates), for all n.
--
-- No analytic theta series is introduced. Turning this free
-- sign-reversing involution into the original E8 shell-count equality
-- still requires a same-source finite enumeration/cardinality theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl; cong; trans)
import Data.Vec as Vec

not : Bool → Bool
not false = true
not true = false

xor : Bool → Bool → Bool
xor false b = b
xor true false = true
xor true true = false

xorNotLeft : ∀ a b → xor (not a) b ≡ not (xor a b)
xorNotLeft false false = refl
xorNotLeft false true = refl
xorNotLeft true false = refl
xorNotLeft true true = refl

natOdd : Nat → Bool
natOdd zero = false
natOdd (suc m) = not (natOdd m)

data OddSignedCoordinate : Set where
  oddSigned : Nat → Bool → OddSignedCoordinate

doubledOddMagnitude : OddSignedCoordinate → Nat
doubledOddMagnitude (oddSigned m _) = suc (m + m)

doubledOddSquare : OddSignedCoordinate → Nat
doubledOddSquare x =
  doubledOddMagnitude x * doubledOddMagnitude x

oddResidueBit : OddSignedCoordinate → Bool
oddResidueBit (oddSigned m negative) = xor (natOdd m) negative

flipOddSign : OddSignedCoordinate → OddSignedCoordinate
flipOddSign (oddSigned m false) = oddSigned m true
flipOddSign (oddSigned m true) = oddSigned m false

flipOddSignInvolutive : (x : OddSignedCoordinate) →
  flipOddSign (flipOddSign x) ≡ x
flipOddSignInvolutive (oddSigned m false) = refl
flipOddSignInvolutive (oddSigned m true) = refl

oddSquareFlipInvariant : (x : OddSignedCoordinate) →
  doubledOddSquare (flipOddSign x) ≡ doubledOddSquare x
oddSquareFlipInvariant (oddSigned m false) = refl
oddSquareFlipInvariant (oddSigned m true) = refl

oddResidueBitFlip :
  (x : OddSignedCoordinate) →
  oddResidueBit (flipOddSign x) ≡ not (oddResidueBit x)
oddResidueBitFlip (oddSigned m false) with natOdd m
... | false = refl
... | true = refl
oddResidueBitFlip (oddSigned m true) with natOdd m
... | false = refl
... | true = refl

doubledOddSquaredNorm :
  ∀ {n} → Vec.Vec OddSignedCoordinate n → Nat
doubledOddSquaredNorm Vec.[] = zero
doubledOddSquaredNorm (x Vec.∷ xs) =
  doubledOddSquare x + doubledOddSquaredNorm xs

oddSumModFourBit :
  ∀ {n} → Vec.Vec OddSignedCoordinate n → Bool
oddSumModFourBit Vec.[] = false
oddSumModFourBit (x Vec.∷ xs) =
  xor (oddResidueBit x) (oddSumModFourBit xs)

flipFirstOdd :
  ∀ {n} → Vec.Vec OddSignedCoordinate (suc n) →
  Vec.Vec OddSignedCoordinate (suc n)
flipFirstOdd (x Vec.∷ xs) = flipOddSign x Vec.∷ xs

flipFirstOddInvolutive :
  ∀ {n} → (xs : Vec.Vec OddSignedCoordinate (suc n)) →
  flipFirstOdd (flipFirstOdd xs) ≡ xs
flipFirstOddInvolutive ((oddSigned m false) Vec.∷ xs) = refl
flipFirstOddInvolutive ((oddSigned m true) Vec.∷ xs) = refl

flipFirstOddPreservesNorm :
  ∀ {n} → (xs : Vec.Vec OddSignedCoordinate (suc n)) →
  doubledOddSquaredNorm (flipFirstOdd xs) ≡ doubledOddSquaredNorm xs
flipFirstOddPreservesNorm ((oddSigned m false) Vec.∷ xs) = refl
flipFirstOddPreservesNorm ((oddSigned m true) Vec.∷ xs) = refl

flipFirstOddReversesParity :
  ∀ {n} → (xs : Vec.Vec OddSignedCoordinate (suc n)) →
  oddSumModFourBit (flipFirstOdd xs) ≡ not (oddSumModFourBit xs)
flipFirstOddReversesParity (x Vec.∷ xs) =
  trans
    (cong (λ bit → xor bit (oddSumModFourBit xs))
      (oddResidueBitFlip x))
    (xorNotLeft (oddResidueBit x) (oddSumModFourBit xs))

record HalfOddShell (n : Nat) : Set where
  constructor half-odd-shell
  field
    coordinates : Vec.Vec OddSignedCoordinate 8
    normIsEightTimesIndex :
      doubledOddSquaredNorm coordinates ≡ 8 * n

open HalfOddShell public

flipHalfOddShell : ∀ {n} → HalfOddShell n → HalfOddShell n
flipHalfOddShell (half-odd-shell coordinates norm) =
  half-odd-shell
    (flipFirstOdd coordinates)
    (trans (flipFirstOddPreservesNorm coordinates) norm)

flipHalfOddShellInvolutive :
  ∀ {n} (shell : HalfOddShell n) →
  coordinates (flipHalfOddShell (flipHalfOddShell shell))
  ≡ coordinates shell
flipHalfOddShellInvolutive (half-odd-shell coords norm) =
  flipFirstOddInvolutive coords

flipHalfOddShellReversesParity :
  ∀ {n} (shell : HalfOddShell n) →
  oddSumModFourBit (coordinates (flipHalfOddShell shell))
  ≡ not (oddSumModFourBit (coordinates shell))
flipHalfOddShellReversesParity (half-odd-shell coords norm) =
  flipFirstOddReversesParity coords

------------------------------------------------------------------------
-- Genuine two-sided parity-selected shell equivalence on unbounded
-- signed-half coordinates. This removes the abstract H0=H2 assumption
-- AT THE COORDINATE-CARRIER LEVEL for every fixed n.
------------------------------------------------------------------------

data SelectedHalfOddShell (n : Nat) (parity : Bool) : Set where
  selected-half-odd-shell :
    (shell : HalfOddShell n) →
    oddSumModFourBit (coordinates shell) ≡ parity →
    SelectedHalfOddShell n parity

flipSelectedHalfOddShell :
  ∀ {n parity} →
  SelectedHalfOddShell n parity →
  SelectedHalfOddShell n (not parity)
flipSelectedHalfOddShell (selected-half-odd-shell shell parityProof) =
  selected-half-odd-shell
    (flipHalfOddShell shell)
    (trans
      (flipHalfOddShellReversesParity shell)
      (cong not parityProof))

EvenHalfOddShell : Nat → Set
EvenHalfOddShell n = SelectedHalfOddShell n false

OddHalfOddShell : Nat → Set
OddHalfOddShell n = SelectedHalfOddShell n true

evenHalfShellToOdd :
  ∀ {n} → EvenHalfOddShell n → OddHalfOddShell n
evenHalfShellToOdd = flipSelectedHalfOddShell

oddHalfShellToEven :
  ∀ {n} → OddHalfOddShell n → EvenHalfOddShell n
oddHalfShellToEven = flipSelectedHalfOddShell

selectedHalfShellCoordinates :
  ∀ {n parity} →
  SelectedHalfOddShell n parity →
  Vec.Vec OddSignedCoordinate 8
selectedHalfShellCoordinates (selected-half-odd-shell shell _) =
  coordinates shell

evenHalfShellTwoSidedOnCoordinates :
  ∀ {n} (shell : EvenHalfOddShell n) →
  selectedHalfShellCoordinates
    (oddHalfShellToEven (evenHalfShellToOdd shell))
  ≡ selectedHalfShellCoordinates shell
evenHalfShellTwoSidedOnCoordinates
  (selected-half-odd-shell shell parityProof) =
  flipHalfOddShellInvolutive shell

oddHalfShellTwoSidedOnCoordinates :
  ∀ {n} (shell : OddHalfOddShell n) →
  selectedHalfShellCoordinates
    (evenHalfShellToOdd (oddHalfShellToEven shell))
  ≡ selectedHalfShellCoordinates shell
oddHalfShellTwoSidedOnCoordinates
  (selected-half-odd-shell shell parityProof) =
  flipHalfOddShellInvolutive shell
