module DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Data.Bool.Base using (T; _∧_; not)
open import Data.Fin.Base as Fin using (Fin; toℕ)
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using
  (ℤ; +_; -_)
import Data.Integer.Properties as ℤP
open import Data.List.Base using
  (List; []; _∷_; allFin; cartesianProductWith; filterᵇ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP
open import Data.Product using (_×_; _,_)
open import Function.Base using (_∘_)
open import Relation.Nullary.Decidable.Core using (T?)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

------------------------------------------------------------------------
-- Exact finite Fourier carriers.
--
-- This module deliberately contains no sampled amplitudes, phases, floating
-- thresholds, or numerical archive dependency.  A shell is represented by a
-- finite cube of integer codes and then filtered by its exact squared norm.
-- The cube [-N , N]^3 contains every lattice point with
-- N² ≤ |k|² < (N + 1)², so it is sufficient for the shell enumeration.
------------------------------------------------------------------------

record LatticeMode3 : Set where
  constructor mkLatticeMode3
  field
    k₁ k₂ k₃ : ℤ

open LatticeMode3 public

modeNeg : LatticeMode3 → LatticeMode3
modeNeg (mkLatticeMode3 k₁ k₂ k₃) =
  mkLatticeMode3 (ℤ.- k₁) (ℤ.- k₂) (ℤ.- k₃)

modeSquaredNorm : LatticeMode3 → ℤ
modeSquaredNorm (mkLatticeMode3 k₁ k₂ k₃) =
  (k₁ ℤ.* k₁) ℤ.+ ((k₂ ℤ.* k₂) ℤ.+ (k₃ ℤ.* k₃))

isZero : ℤ → Bool
isZero (+ 0) = true
isZero _ = false

nonzeroMode? : LatticeMode3 → Bool
nonzeroMode? (mkLatticeMode3 k₁ k₂ k₃) =
  not (isZero k₁ ∧ (isZero k₂ ∧ isZero k₃))

shellLowerBound : Nat → ℤ
shellLowerBound N = + (N * N)

shellUpperBound : Nat → ℤ
shellUpperBound N = + ((suc N) * (suc N))

inExactShell? : Nat → LatticeMode3 → Bool
inExactShell? N k =
  (shellLowerBound N ℤ.≤ᵇ modeSquaredNorm k) ∧
  ((modeSquaredNorm k ℤ.<ᵇ shellUpperBound N) ∧ nonzeroMode? k)

-- Fin (2N + 1) is decoded to the exact integer interval [-N , N].
coordinateCodeBound : Nat → Nat
coordinateCodeBound N = suc (N + N)

decodeCoordinate : (N : Nat) → Fin (coordinateCodeBound N) → ℤ
decodeCoordinate N i = Fin.toℕ i ℤ.⊖ N

-- Subtracting the fixed cutoff radius is injective on coordinate codes.  The
-- proof restores the same integer radius on both sides and then uses the
-- ordinary injectivity of `Fin.toℕ`.
decodeCoordinateInjective :
  (N : Nat) → {i j : Fin (coordinateCodeBound N)} →
  decodeCoordinate N i ≡ decodeCoordinate N j → i ≡ j
decodeCoordinateInjective N {i} {j} decodedEqual =
  FinP.toℕ-injective integerCodeEqual
  where
  restoreCoordinate :
    (m : Nat) → + m ≡ (m ℤ.⊖ N) ℤ.+ (+ N)
  restoreCoordinate m =
    sym
      (trans
        (cong (λ z → z ℤ.+ (+ N)) (sym (ℤP.m-n≡m⊖n m N)))
        (trans
          (ℤP.+-assoc (+ m) (- (+ N)) (+ N))
          (trans
            (cong (λ z → (+ m) ℤ.+ z) (ℤP.+-inverseˡ (+ N)))
            (ℤP.+-identityʳ (+ m)))))

  integerCodeEqual : Fin.toℕ i ≡ Fin.toℕ j
  integerCodeEqual = ℤP.+-injective
    (trans
      (restoreCoordinate (Fin.toℕ i))
      (trans
        (cong (λ z → z ℤ.+ (+ N)) decodedEqual)
        (sym (restoreCoordinate (Fin.toℕ j)))))

CubeCode : Nat → Set
CubeCode N =
  Fin (coordinateCodeBound N) ×
  (Fin (coordinateCodeBound N) × Fin (coordinateCodeBound N))

decodeCubeCode : (N : Nat) → CubeCode N → LatticeMode3
decodeCubeCode N (i , j , k) =
  mkLatticeMode3
    (decodeCoordinate N i)
    (decodeCoordinate N j)
    (decodeCoordinate N k)

cubeCodes : (N : Nat) → List (CubeCode N)
cubeCodes N =
  cartesianProductWith _,_
    (allFin (coordinateCodeBound N))
    (cartesianProductWith _,_
      (allFin (coordinateCodeBound N))
      (allFin (coordinateCodeBound N)))

pairConstructorInjective :
  {A B : Set} → {a b : A} → {x y : B} →
  (a , x) ≡ (b , y) → (a ≡ b) × (x ≡ y)
pairConstructorInjective refl = refl , refl

cubeCodesUnique : (N : Nat) → Unique (cubeCodes N)
cubeCodesUnique N =
  UniqueP.cartesianProductWith⁺ _,_ pairConstructorInjective
    (UniqueP.allFin⁺ (coordinateCodeBound N))
    (UniqueP.cartesianProductWith⁺ _,_ pairConstructorInjective
      (UniqueP.allFin⁺ (coordinateCodeBound N))
      (UniqueP.allFin⁺ (coordinateCodeBound N)))

decodeCubeCodeInjective :
  (N : Nat) → {x y : CubeCode N} →
  decodeCubeCode N x ≡ decodeCubeCode N y → x ≡ y
decodeCubeCodeInjective N {i , j , k} {i′ , j′ , k′} decodedEqual =
  cong₂ _,_
    (decodeCoordinateInjective N (cong k₁ decodedEqual))
    (cong₂ _,_
      (decodeCoordinateInjective N (cong k₂ decodedEqual))
      (decodeCoordinateInjective N (cong k₃ decodedEqual)))

exactShellModes : (N : Nat) → List LatticeMode3
exactShellModes N =
  filterᵇ (inExactShell? N)
    (Data.List.Base.map (decodeCubeCode N) (cubeCodes N))

exactShellModesUnique : (N : Nat) → Unique (exactShellModes N)
exactShellModesUnique N =
  UniqueP.filter⁺ (T? ∘ inExactShell? N)
    (UniqueP.map⁺ (decodeCubeCodeInjective N) (cubeCodesUnique N))

record LatticeTriad : Set where
  constructor mkLatticeTriad
  field
    left right out : LatticeMode3

open LatticeTriad public

triadSum : LatticeTriad → LatticeMode3
triadSum (mkLatticeTriad left right out) =
  mkLatticeMode3
    ((k₁ left ℤ.+ k₁ right) ℤ.+ k₁ out)
    ((k₂ left ℤ.+ k₂ right) ℤ.+ k₂ out)
    ((k₃ left ℤ.+ k₃ right) ℤ.+ k₃ out)

zeroMode? : LatticeMode3 → Bool
zeroMode? (mkLatticeMode3 k₁ k₂ k₃) =
  isZero k₁ ∧ (isZero k₂ ∧ isZero k₃)

zeroSum? : LatticeTriad → Bool
zeroSum? τ = zeroMode? (triadSum τ)

triadNeg : LatticeTriad → LatticeTriad
triadNeg (mkLatticeTriad left right out) =
  mkLatticeTriad (modeNeg left) (modeNeg right) (modeNeg out)

triadCycle : LatticeTriad → LatticeTriad
triadCycle (mkLatticeTriad left right out) =
  mkLatticeTriad right out left

triadSwap : LatticeTriad → LatticeTriad
triadSwap (mkLatticeTriad left right out) =
  mkLatticeTriad right left out

-- The retained sector is intentionally an input to the exact construction.
-- The Python diagnostics may have used additional orientation, shell-pair,
-- or coherence restrictions.  Those restrictions must be represented here
-- before this enumeration can be identified with a physical NS operator.
record ExactRetainedSectorLaw (N : Nat) : Set₁ where
  field
    retained? : LatticeTriad → Bool

    -- These are theorem obligations, not Boolean receipts.  They prevent a
    -- sector selected by an arbitrary ordering or a sampled threshold from
    -- being mistaken for a physical retained-triad definition.
    -- Cycle and swap generate all permutations, so these two equalities give
    -- a concrete, checkable permutation law rather than an opaque receipt.
    cycleInvariant :
      (τ : LatticeTriad) → retained? (triadCycle τ) ≡ retained? τ
    swapInvariant :
      (τ : LatticeTriad) → retained? (triadSwap τ) ≡ retained? τ
    realityInvariant :
      (τ : LatticeTriad) → retained? (triadNeg τ) ≡ retained? τ
    zeroSumRequired :
      (τ : LatticeTriad) → retained? τ ≡ true → zeroSum? τ ≡ true

open ExactRetainedSectorLaw public

-- Candidate only: all exact zero-sum triples whose three modes are supplied
-- by the shell enumeration.  It is not installed as the canonical physical
-- sector until its symmetry laws are proved against the intended NS model.
allZeroSumSameShellSector? : LatticeTriad → Bool
allZeroSumSameShellSector? = zeroSum?

exactRetainedTriads : (N : Nat) → ExactRetainedSectorLaw N → List LatticeTriad
exactRetainedTriads N sector =
  filterᵇ (retained? sector)
    (filterᵇ zeroSum?
    (cartesianProductWith
      (λ left pair → mkLatticeTriad left (Data.Product.proj₁ pair)
        (Data.Product.proj₂ pair))
      (exactShellModes N)
      (cartesianProductWith _,_ (exactShellModes N) (exactShellModes N))))

------------------------------------------------------------------------
-- Explicit theorem targets for the integer enumeration.  They are separate
-- from numerical validation and remain fail-closed until the bounded-integer
-- and filtered-list proofs are supplied.
------------------------------------------------------------------------

ShellMember : Nat → LatticeMode3 → Set
ShellMember N k = inExactShell? N k ≡ true

RetainedTriadMember : (N : Nat) → ExactRetainedSectorLaw N → LatticeTriad → Set
RetainedTriadMember N sector τ =
  ShellMember N (left τ) ×
  (ShellMember N (right τ) ×
   (ShellMember N (out τ) ×
    (zeroSum? τ ≡ true × retained? sector τ ≡ true)))

triadEnumerationFinite : (N : Nat) → ExactRetainedSectorLaw N → List LatticeTriad
triadEnumerationFinite = exactRetainedTriads

record ExactLatticeShellTriadEnumeration
    (N : Nat) (sector : ExactRetainedSectorLaw N) : Set₁ where
  field
    modes : List LatticeMode3
    triads : List LatticeTriad
    modesAreExactShell : modes ≡ exactShellModes N
    triadsAreExactRetained : triads ≡ exactRetainedTriads N sector
    triadEnumerationSound :
      (τ : LatticeTriad) →
      τ ∈ triads → RetainedTriadMember N sector τ
    triadEnumerationComplete :
      (τ : LatticeTriad) →
      RetainedTriadMember N sector τ → τ ∈ triads
    triadEnumerationNoDuplicates : Unique triads

exactLatticeShellTriadsClosed : Bool
exactLatticeShellTriadsClosed = false

exactLatticeShellTriadsClosedIsFalse :
  exactLatticeShellTriadsClosed ≡ false
exactLatticeShellTriadsClosedIsFalse = refl
