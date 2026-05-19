module DASHI.Physics.Toy.ScalarHarmonic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (_≤_; _<_; z≤n; s≤s)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import DASHI.Physics.Toy.Recovery as TR

defectScalar : Trit → Nat
defectScalar zer = zero
defectScalar neg = suc zero
defectScalar pos = suc zero

scalarStep : Trit → Trit
scalarStep _ = zer

ScalarRecoveredLaw : Set
ScalarRecoveredLaw = ∀ x → scalarStep x ≡ x → x ≡ zer

scalarStable : Trit → Set
scalarStable x = x ≡ zer

scalarInv : Trit → Set
scalarInv _ = ⊤

scalarInv-preserved : ∀ {x} → scalarInv x → scalarInv (scalarStep x)
scalarInv-preserved _ = tt

scalarDefect-desc : ∀ {x} → scalarInv x → defectScalar (scalarStep x) ≤ defectScalar x
scalarDefect-desc {zer} _ = z≤n
scalarDefect-desc {neg} _ = z≤n
scalarDefect-desc {pos} _ = z≤n

scalarDefect-strict :
  ∀ {x} → scalarInv x → defectScalar x TR.≢ zero → defectScalar (scalarStep x) < defectScalar x
scalarDefect-strict {zer} _ nz = ⊥-elim (nz refl)
scalarDefect-strict {neg} _ _ = s≤s z≤n
scalarDefect-strict {pos} _ _ = s≤s z≤n

scalarStable-fixed : ∀ {x} → scalarStable x → scalarStep x ≡ x
scalarStable-fixed refl = refl

scalarStable-from-zero : ∀ {x} → scalarInv x → defectScalar x ≡ zero → scalarStable x
scalarStable-from-zero {zer} _ refl = refl
scalarStable-from-zero {neg} _ ()
scalarStable-from-zero {pos} _ ()

scalarRecovered-from-stable : ∀ {x} → scalarStable x → ScalarRecoveredLaw
scalarRecovered-from-stable {x} stable zer refl = refl
scalarRecovered-from-stable {x} stable neg ()
scalarRecovered-from-stable {x} stable pos ()

unique-harmonic-state : ∀ x → scalarStep x ≡ x → x ≡ zer
unique-harmonic-state zer refl = refl
unique-harmonic-state neg ()
unique-harmonic-state pos ()

ScalarTheory : TR.ToyTheory
ScalarTheory =
  record
    { X = Trit
    ; Obs = Trit
    ; RecoveredLaw = ScalarRecoveredLaw
    ; step = scalarStep
    ; defect = defectScalar
    ; obs = λ x → x
    ; inv = scalarInv
    ; inv-preserved = λ {x} → scalarInv-preserved {x}
    ; defect-desc = λ {x} → scalarDefect-desc {x}
    ; defect-strict = λ {x} → scalarDefect-strict {x}
    ; stable = scalarStable
    ; stable-fixed = λ {x} → scalarStable-fixed {x}
    ; stable-from-zero-defect = λ {x} → scalarStable-from-zero {x}
    ; recovered-from-stable = λ {x} → scalarRecovered-from-stable {x}
    }

scalarStablePoint : TR.StablePoint ScalarTheory
scalarStablePoint =
  record
    { point = zer
    ; fixed = refl
    ; law = unique-harmonic-state
    }

scalarRecovery : TR.RecoveryAxiom ScalarTheory
scalarRecovery =
  record
    { stable-point = λ x _ → scalarStablePoint
    }

harmonic-vacuum-recovery :
  ∀ x →
  TR.RecoveredLaw ScalarTheory
harmonic-vacuum-recovery x = TR.StablePoint.law (TR.RecoveryAxiom.stable-point scalarRecovery x tt)
