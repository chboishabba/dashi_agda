module DASHI.Physics.Closure.NSTriadKNCanonicalRealityOrbitCarrierRound63Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- ROUND 63 A0 CONTRIBUTION
--
-- Round62 proved that the unrestricted reconstructed-state list is not a
-- fixed-dimensional Picard coordinate carrier: it stores an RHS value for both
-- members of every reality orbit and then reconstructs both signs again.
--
-- This file constructs the required fixed-cutoff one-sheet carrier directly
-- from the literal duplicate-free cutoff cube.  The canonical representative
-- of a nonzero orbit {k,-k} is the member whose FIRST NONZERO coordinate
-- (x, then y, then z) is positive.
--
-- The construction proves:
--
--   * zero is never a representative;
--   * representatives are literal cutoff modes;
--   * the representative list is duplicate-free;
--   * negation flips positive/negative orientation;
--   * every nonzero cutoff mode has either itself or its negative in the list;
--   * never both k and -k occur in the representative list.
--
-- Hence each nonzero k ~ -k reality orbit is represented exactly once without
-- introducing a quotient type or a choice axiom.  The next A0 weld is only to
-- map the already-proved reality-compatible Galerkin RHS over this fixed list.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer.Base using (ℤ; +_; -[1+_]; -_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube

data Orientation : Set where
  negativeOrientation zeroOrientation positiveOrientation : Orientation

flipOrientation : Orientation → Orientation
flipOrientation negativeOrientation = positiveOrientation
flipOrientation zeroOrientation = zeroOrientation
flipOrientation positiveOrientation = negativeOrientation

integerOrientation : ℤ → Orientation
integerOrientation (+ zero) = zeroOrientation
integerOrientation (+ (suc n)) = positiveOrientation
integerOrientation (-[1+ n ]) = negativeOrientation

integerOrientationNegate :
  (z : ℤ) →
  integerOrientation (- z) ≡ flipOrientation (integerOrientation z)
integerOrientationNegate (+ zero) = refl
integerOrientationNegate (+ (suc n)) = refl
integerOrientationNegate (-[1+ n ]) = refl

firstNonzeroOrientation : Orientation → Orientation → Orientation → Orientation
firstNonzeroOrientation negativeOrientation y z = negativeOrientation
firstNonzeroOrientation positiveOrientation y z = positiveOrientation
firstNonzeroOrientation zeroOrientation negativeOrientation z = negativeOrientation
firstNonzeroOrientation zeroOrientation positiveOrientation z = positiveOrientation
firstNonzeroOrientation zeroOrientation zeroOrientation z = z

firstNonzeroFlip :
  (x y z : Orientation) →
  firstNonzeroOrientation (flipOrientation x) (flipOrientation y) (flipOrientation z)
  ≡ flipOrientation (firstNonzeroOrientation x y z)
firstNonzeroFlip negativeOrientation y z = refl
firstNonzeroFlip positiveOrientation y z = refl
firstNonzeroFlip zeroOrientation negativeOrientation z = refl
firstNonzeroFlip zeroOrientation positiveOrientation z = refl
firstNonzeroFlip zeroOrientation zeroOrientation negativeOrientation = refl
firstNonzeroFlip zeroOrientation zeroOrientation zeroOrientation = refl
firstNonzeroFlip zeroOrientation zeroOrientation positiveOrientation = refl

modeOrientation : Z3.FourierMode → Orientation
modeOrientation (Z3.mode x y z) =
  firstNonzeroOrientation
    (integerOrientation x)
    (integerOrientation y)
    (integerOrientation z)

modeOrientationNegate :
  (k : Z3.FourierMode) →
  modeOrientation (Z3.negateMode k) ≡ flipOrientation (modeOrientation k)
modeOrientationNegate (Z3.mode x y z)
  rewrite integerOrientationNegate x
        | integerOrientationNegate y
        | integerOrientationNegate z =
  firstNonzeroFlip
    (integerOrientation x)
    (integerOrientation y)
    (integerOrientation z)

modeOrientationZeroExact :
  ∀ {k : Z3.FourierMode} →
  modeOrientation k ≡ zeroOrientation →
  k ≡ Z3.zeroMode
modeOrientationZeroExact {Z3.mode (+ zero) (+ zero) (+ zero)} proof = refl
modeOrientationZeroExact {Z3.mode (+ zero) (+ zero) (+ (suc n))} ()
modeOrientationZeroExact {Z3.mode (+ zero) (+ zero) (-[1+ n ])} ()
modeOrientationZeroExact {Z3.mode (+ zero) (+ (suc n)) z} ()
modeOrientationZeroExact {Z3.mode (+ zero) (-[1+ n ]) z} ()
modeOrientationZeroExact {Z3.mode (+ (suc n)) y z} ()
modeOrientationZeroExact {Z3.mode (-[1+ n ]) y z} ()

nonzeroOrientation :
  ∀ {k : Z3.FourierMode} →
  Z3.NonZeroMode k →
  (modeOrientation k ≡ negativeOrientation)
  ⊎ (modeOrientation k ≡ positiveOrientation)
nonzeroOrientation {k} nonzero with modeOrientation k in orientationProof
... | negativeOrientation = inj₁ refl
... | positiveOrientation = inj₂ refl
... | zeroOrientation =
  ⊥-elim
    (Z3.NonZeroMode.notZero nonzero
      (modeOrientationZeroExact orientationProof))

canonicalRepresentativeSelect : Z3.FourierMode → Bool
canonicalRepresentativeSelect k with modeOrientation k
... | positiveOrientation = true
... | negativeOrientation = false
... | zeroOrientation = false

canonicalSelectTrueOrientation :
  ∀ {k} → canonicalRepresentativeSelect k ≡ true →
  modeOrientation k ≡ positiveOrientation
canonicalSelectTrueOrientation {k} proof with modeOrientation k
... | positiveOrientation = refl
... | negativeOrientation = falseNotTrue proof
... | zeroOrientation = falseNotTrue proof
  where
  falseNotTrue : false ≡ true → modeOrientation k ≡ positiveOrientation
  falseNotTrue ()

positiveOrientationSelects :
  ∀ {k} → modeOrientation k ≡ positiveOrientation →
  canonicalRepresentativeSelect k ≡ true
positiveOrientationSelects {k} proof with modeOrientation k
... | positiveOrientation = refl
... | negativeOrientation = orientationMismatch proof
... | zeroOrientation = orientationMismatch proof
  where
  orientationMismatch :
    {o : Orientation} → o ≡ positiveOrientation →
    canonicalRepresentativeSelect k ≡ true
  orientationMismatch ()

filterRepresentatives : List Z3.FourierMode → List Z3.FourierMode
filterRepresentatives [] = []
filterRepresentatives (k ∷ ks) with canonicalRepresentativeSelect k
... | true = k ∷ filterRepresentatives ks
... | false = filterRepresentatives ks

canonicalRealityOrbitModes : Nat → List Z3.FourierMode
canonicalRealityOrbitModes cutoff =
  filterRepresentatives (Cube.cutoffModes cutoff)

filterRepresentativeMemberOriginal :
  ∀ {k modes} →
  k Cube.∈ filterRepresentatives modes → k Cube.∈ modes
filterRepresentativeMemberOriginal {modes = []} ()
filterRepresentativeMemberOriginal {modes = head ∷ tail} member
  with canonicalRepresentativeSelect head
... | true with member
...   | Cube.here equality = Cube.here equality
...   | Cube.there rest = Cube.there (filterRepresentativeMemberOriginal rest)
... | false = Cube.there (filterRepresentativeMemberOriginal member)

filterRepresentativeSound :
  ∀ {k modes} →
  k Cube.∈ filterRepresentatives modes →
  canonicalRepresentativeSelect k ≡ true
filterRepresentativeSound {modes = []} ()
filterRepresentativeSound {modes = head ∷ tail} member
  with canonicalRepresentativeSelect head in headSelected
... | true with member
...   | Cube.here refl = headSelected
...   | Cube.there rest = filterRepresentativeSound rest
... | false = filterRepresentativeSound member

filterRepresentativeComplete :
  ∀ {k modes} →
  k Cube.∈ modes →
  canonicalRepresentativeSelect k ≡ true →
  k Cube.∈ filterRepresentatives modes
filterRepresentativeComplete {modes = []} () selected
filterRepresentativeComplete {modes = head ∷ tail}
  (Cube.here refl) selected
  with canonicalRepresentativeSelect head
... | true = Cube.here refl
... | false with selected
...   | ()
filterRepresentativeComplete {modes = head ∷ tail}
  (Cube.there member) selected
  with canonicalRepresentativeSelect head
... | true = Cube.there (filterRepresentativeComplete member selected)
... | false = filterRepresentativeComplete member selected

filterRepresentativesNoDuplicates :
  ∀ {modes} → Cube.NoDuplicates modes →
  Cube.NoDuplicates (filterRepresentatives modes)
filterRepresentativesNoDuplicates Cube.unique[] = Cube.unique[]
filterRepresentativesNoDuplicates
  (Cube.unique∷ {x = head} {xs = tail} fresh rest)
  with canonicalRepresentativeSelect head
... | true =
  Cube.unique∷
    (λ member → fresh (filterRepresentativeMemberOriginal member))
    (filterRepresentativesNoDuplicates rest)
... | false = filterRepresentativesNoDuplicates rest

canonicalRealityOrbitModesNoDuplicates :
  (cutoff : Nat) →
  Cube.NoDuplicates (canonicalRealityOrbitModes cutoff)
canonicalRealityOrbitModesNoDuplicates cutoff =
  filterRepresentativesNoDuplicates (Cube.cutoffModeEnumerationNoDuplicates cutoff)

canonicalRepresentativeInCutoff :
  ∀ {cutoff k} →
  k Cube.∈ canonicalRealityOrbitModes cutoff →
  k Cube.∈ Cube.cutoffModes cutoff
canonicalRepresentativeInCutoff = filterRepresentativeMemberOriginal

canonicalRepresentativePositive :
  ∀ {cutoff k} →
  k Cube.∈ canonicalRealityOrbitModes cutoff →
  modeOrientation k ≡ positiveOrientation
canonicalRepresentativePositive member =
  canonicalSelectTrueOrientation (filterRepresentativeSound member)

zeroNeverCanonical :
  (cutoff : Nat) →
  Z3.zeroMode Cube.∉ canonicalRealityOrbitModes cutoff
zeroNeverCanonical cutoff member with canonicalRepresentativePositive member
... | ()

positiveNegatesToNegative :
  ∀ {k} →
  modeOrientation k ≡ positiveOrientation →
  modeOrientation (Z3.negateMode k) ≡ negativeOrientation
positiveNegatesToNegative {k} positive =
  trans
    (modeOrientationNegate k)
    (cong flipOrientation positive)

negativeNegatesToPositive :
  ∀ {k} →
  modeOrientation k ≡ negativeOrientation →
  modeOrientation (Z3.negateMode k) ≡ positiveOrientation
negativeNegatesToPositive {k} negative =
  trans
    (modeOrientationNegate k)
    (cong flipOrientation negative)

positiveNotNegative : positiveOrientation ≡ negativeOrientation → ⊥
positiveNotNegative ()

canonicalAndNegativeCannotBothOccur :
  ∀ {cutoff k} →
  k Cube.∈ canonicalRealityOrbitModes cutoff →
  Z3.negateMode k Cube.∈ canonicalRealityOrbitModes cutoff →
  ⊥
canonicalAndNegativeCannotBothOccur kMember negMember =
  positiveNotNegative
    (trans
      (sym (canonicalRepresentativePositive negMember))
      (positiveNegatesToNegative (canonicalRepresentativePositive kMember)))

nonzeroCutoffModeHasCanonicalSheet :
  ∀ {cutoff k} →
  k Cube.∈ Cube.cutoffModes cutoff →
  Z3.NonZeroMode k →
  (k Cube.∈ canonicalRealityOrbitModes cutoff)
  ⊎ (Z3.negateMode k Cube.∈ canonicalRealityOrbitModes cutoff)
nonzeroCutoffModeHasCanonicalSheet {cutoff} {k} member nonzero
  with nonzeroOrientation nonzero
... | inj₂ positive =
  inj₁
    (filterRepresentativeComplete member (positiveOrientationSelects positive))
... | inj₁ negative =
  let
    negMember : Z3.negateMode k Cube.∈ Cube.cutoffModes cutoff
    negMember = Cube.cutoffClosedUnderNegation cutoff k member

    negPositive :
      modeOrientation (Z3.negateMode k) ≡ positiveOrientation
    negPositive = negativeNegatesToPositive negative
  in
  inj₂
    (filterRepresentativeComplete negMember
      (positiveOrientationSelects negPositive))

canonicalRealityOrbitCarrierConstructed : Bool
canonicalRealityOrbitCarrierConstructed = true

canonicalRealityOrbitCarrierExactlyOneSheet : Bool
canonicalRealityOrbitCarrierExactlyOneSheet = true

canonicalRealityOrbitCarrierConstructedIsTrue :
  canonicalRealityOrbitCarrierConstructed ≡ true
canonicalRealityOrbitCarrierConstructedIsTrue = refl

canonicalRealityOrbitCarrierExactlyOneSheetIsTrue :
  canonicalRealityOrbitCarrierExactlyOneSheet ≡ true
canonicalRealityOrbitCarrierExactlyOneSheetIsTrue = refl
