module DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (ℤ; +_; -[1+_])
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical

open Cube using (_∈_)

------------------------------------------------------------------------
-- Executable exact equality on Z^3.
------------------------------------------------------------------------

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc n) = false
natEqual (suc m) zero = false
natEqual (suc m) (suc n) = natEqual m n

natEqualSound : ∀ {m n} → natEqual m n ≡ true → m ≡ n
natEqualSound {zero} {zero} proof = refl
natEqualSound {zero} {suc n} ()
natEqualSound {suc m} {zero} ()
natEqualSound {suc m} {suc n} proof =
  cong suc (natEqualSound proof)

natEqualRefl : ∀ n → natEqual n n ≡ true
natEqualRefl zero = refl
natEqualRefl (suc n) = natEqualRefl n

integerEqual : ℤ → ℤ → Bool
integerEqual (+ m) (+ n) = natEqual m n
integerEqual (+ m) (-[1+ n ]) = false
integerEqual (-[1+ m ]) (+ n) = false
integerEqual (-[1+ m ]) (-[1+ n ]) = natEqual m n

integerEqualSound : ∀ {a b} → integerEqual a b ≡ true → a ≡ b
integerEqualSound {+ m} {+ n} proof =
  cong +_ (natEqualSound proof)
integerEqualSound {+ m} {-[1+ n ]} ()
integerEqualSound {-[1+ m ]} {+ n} ()
integerEqualSound {-[1+ m ]} {-[1+ n ]} proof =
  cong -[1+_] (natEqualSound proof)

integerEqualRefl : ∀ z → integerEqual z z ≡ true
integerEqualRefl (+ n) = natEqualRefl n
integerEqualRefl (-[1+ n ]) = natEqualRefl n

infixr 5 _and_

_and_ : Bool → Bool → Bool
true and b = b
false and b = false

andTrueLeft : ∀ {a b} → a and b ≡ true → a ≡ true
andTrueLeft {true} proof = refl
andTrueLeft {false} ()

andTrueRight : ∀ {a b} → a and b ≡ true → b ≡ true
andTrueRight {true} proof = proof
andTrueRight {false} ()

modeEqual : Z3.FourierMode → Z3.FourierMode → Bool
modeEqual a b =
  integerEqual (Z3.kx a) (Z3.kx b)
  and
  (integerEqual (Z3.ky a) (Z3.ky b)
  and integerEqual (Z3.kz a) (Z3.kz b))

modeExt :
  ∀ {a b : Z3.FourierMode} →
  Z3.kx a ≡ Z3.kx b →
  Z3.ky a ≡ Z3.ky b →
  Z3.kz a ≡ Z3.kz b →
  a ≡ b
modeExt {Z3.mode ax ay az} {Z3.mode .ax .ay .az} refl refl refl = refl

modeEqualSound : ∀ {a b} → modeEqual a b ≡ true → a ≡ b
modeEqualSound proof =
  modeExt
    (integerEqualSound (andTrueLeft proof))
    (integerEqualSound (andTrueLeft (andTrueRight proof)))
    (integerEqualSound (andTrueRight (andTrueRight proof)))

modeEqualRefl : ∀ mode → modeEqual mode mode ≡ true
modeEqualRefl (Z3.mode x y z)
  rewrite integerEqualRefl x
        | integerEqualRefl y
        | integerEqualRefl z = refl

modeEqualComplete : ∀ {a b} → a ≡ b → modeEqual a b ≡ true
modeEqualComplete {a} refl = modeEqualRefl a

------------------------------------------------------------------------
-- Literal output fibre of the physical triad enumeration.
------------------------------------------------------------------------

filterOutput :
  Z3.FourierMode →
  List Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence
filterOutput output [] = []
filterOutput output (τ ∷ rest) with modeEqual (Physical.k τ) output
... | true = τ ∷ filterOutput output rest
... | false = filterOutput output rest

physicalOutputFiber :
  Nat → Z3.FourierMode → List Physical.PhysicalTriadIncidence
physicalOutputFiber cutoff output =
  filterOutput output (Physical.physicalTriadEnumeration cutoff)

filterOutputSound :
  ∀ {output items τ} →
  τ ∈ filterOutput output items →
  Physical.k τ ≡ output
filterOutputSound {items = []} ()
filterOutputSound {output} {items = head ∷ tail} {τ} member
  with modeEqual (Physical.k head) output
... | true with member
...   | Cube.here equality =
      trans
        (cong Physical.k equality)
        (modeEqualSound refl)
...   | Cube.there rest =
      filterOutputSound rest
... | false =
      filterOutputSound member

physicalOutputFiberSound :
  ∀ {cutoff output τ} →
  τ ∈ physicalOutputFiber cutoff output →
  Physical.k τ ≡ output
physicalOutputFiberSound = filterOutputSound

filterOutputComplete :
  ∀ {output items τ} →
  τ ∈ items →
  Physical.k τ ≡ output →
  τ ∈ filterOutput output items
filterOutputComplete {items = []} ()
filterOutputComplete {output} {items = head ∷ tail} {τ}
  member outputEquality
  with modeEqual (Physical.k head) output
... | true with member
...   | Cube.here equality = Cube.here equality
...   | Cube.there rest = Cube.there (filterOutputComplete rest outputEquality)
... | false with member
...   | Cube.there rest = filterOutputComplete rest outputEquality
...   | Cube.here equality
      with modeEqualComplete
        (trans (sym (cong Physical.k equality)) outputEquality)
...     | ()

physicalOutputFiberComplete :
  ∀ {cutoff output τ} →
  τ ∈ Physical.physicalTriadEnumeration cutoff →
  Physical.k τ ≡ output →
  τ ∈ physicalOutputFiber cutoff output
physicalOutputFiberComplete = filterOutputComplete

physicalOutputFiberImplemented : Bool
physicalOutputFiberImplemented = true

physicalOutputFiberImplementedIsTrue :
  physicalOutputFiberImplemented ≡ true
physicalOutputFiberImplementedIsTrue = refl
