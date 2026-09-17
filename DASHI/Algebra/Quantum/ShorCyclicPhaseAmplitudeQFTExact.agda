module DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin)
import Data.Fin.Properties as FinP
open import Data.List.Base using (List; []; _∷_; allFin)
open import Relation.Nullary using (Dec; yes; no)

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.FiniteQuantumRegister as Finite
import DASHI.Algebra.Quantum.QuantumFourierTransformFinite as QFT
import DASHI.Algebra.Quantum.ShorCyclicExponentBasisExact as Cyclic

------------------------------------------------------------------------
-- CYCLIC PHASE / AMPLITUDE QFT CONTRACT
--
-- This is the first Shor owner whose forward action is pinned to the literal
-- cyclic character kernel.  It therefore cannot be inhabited by choosing the
-- identity transform merely because the old FiniteFourierTransform interface
-- asks only for an invertible endomap.
--
-- The exponent coordinate is Fin Q.  The target coordinate is independent and
-- finite: either the distinguished clean slot or a residue in Fin N.  A state
-- is an actual coefficient function on that finite computational basis.
--
-- For every target slot y,
--
--   F psi (k,y) = sum_x normalisation * phase(k,x) * psi(x,y)
--
-- and the inverse is the same finite sum with inversePhase.  The target slot is
-- therefore retained definitionally by the QFT.
--
-- What remains external is deliberately narrow: one concrete coefficient
-- algebra, root-of-unity character table/normalisation, and proofs that these
-- two literal finite sums are inverse.  DASHI already has an external normalized
-- cyclic DFT theorem receipt; a later same-object weld may use that theorem to
-- inhabit `CyclicPhaseInversionAuthority`.  This module does not re-prove or
-- silently import that complex-matrix result.
------------------------------------------------------------------------

data FiniteTargetSlot (N : Nat) : Set where
  cleanSlot : FiniteTargetSlot N
  residueSlot : Fin N → FiniteTargetSlot N

targetSlotDecEq :
  ∀ {N} →
  (left right : FiniteTargetSlot N) →
  Dec (left ≡ right)
targetSlotDecEq cleanSlot cleanSlot = yes refl
targetSlotDecEq cleanSlot (residueSlot right) = no (λ ())
targetSlotDecEq (residueSlot left) cleanSlot = no (λ ())
targetSlotDecEq (residueSlot left) (residueSlot right)
  with FinP._≟_ left right
... | yes refl = yes refl
... | no different = no (λ where refl → different refl)

record CyclicPhaseCoefficientAuthority
    (Coefficient : Set)
    (Q : Nat) : Set₁ where
  constructor cyclicPhaseCoefficientAuthority
  field
    zeroCoefficient : Coefficient
    oneCoefficient : Coefficient
    addCoefficient : Coefficient → Coefficient → Coefficient
    multiplyCoefficient : Coefficient → Coefficient → Coefficient

    normalisation : Coefficient
    phase : Fin Q → Fin Q → Coefficient
    inversePhase : Fin Q → Fin Q → Coefficient

open CyclicPhaseCoefficientAuthority public

sumCoefficients :
  ∀ {Coefficient : Set} {Q : Nat} →
  CyclicPhaseCoefficientAuthority Coefficient Q →
  (Fin Q → Coefficient) →
  List (Fin Q) → Coefficient
sumCoefficients A term [] = zeroCoefficient A
sumCoefficients A term (x ∷ xs) =
  addCoefficient A (term x) (sumCoefficients A term xs)

record CyclicPhaseAmplitudeState
    {Coefficient : Set}
    (Q N : Nat)
    (A : CyclicPhaseCoefficientAuthority Coefficient Q) : Set where
  constructor cyclicPhaseAmplitudeState
  field
    classicalTag : Fin Q
    amplitude : Fin Q → FiniteTargetSlot N → Coefficient

open CyclicPhaseAmplitudeState public

basisCoefficient :
  ∀ {Coefficient Q N}
    (A : CyclicPhaseCoefficientAuthority Coefficient Q) →
  Fin Q → FiniteTargetSlot N →
  Fin Q → FiniteTargetSlot N → Coefficient
basisCoefficient A x y k slot
  with FinP._≟_ x k | targetSlotDecEq y slot
... | yes refl | yes refl = oneCoefficient A
... | _ | _ = zeroCoefficient A

cleanBasisAmplitude :
  ∀ {Q N Coefficient}
    (A : CyclicPhaseCoefficientAuthority Coefficient Q) →
  Fin Q → CyclicPhaseAmplitudeState Q N A
cleanBasisAmplitude A x =
  cyclicPhaseAmplitudeState x
    (basisCoefficient A x cleanSlot)

basisAmplitude :
  ∀ {Q N Coefficient}
    (qNonZero : B369.NonZero Q) →
    (nNonZero : B369.NonZero N) →
    (A : CyclicPhaseCoefficientAuthority Coefficient Q) →
  Fin Q → Fin N → CyclicPhaseAmplitudeState Q N A
basisAmplitude qNonZero nNonZero A x y =
  cyclicPhaseAmplitudeState x
    (basisCoefficient A x (residueSlot y))

cyclicPhaseAmplitudeRegister :
  ∀ {Q N Coefficient} →
  (qNonZero : B369.NonZero Q) →
  (nNonZero : B369.NonZero N) →
  (A : CyclicPhaseCoefficientAuthority Coefficient Q) →
  Finite.FiniteQuantumRegister
    (Cyclic.cyclicExponentBasis Q qNonZero)
cyclicPhaseAmplitudeRegister {Q} {N} qNonZero nNonZero A = record
  { State = CyclicPhaseAmplitudeState Q N A
  ; prepare = cleanBasisAmplitude A
  ; observe = classicalTag
  ; observePrepared = λ x → refl
  }

forwardAmplitude :
  ∀ {Coefficient Q N}
    (A : CyclicPhaseCoefficientAuthority Coefficient Q) →
  CyclicPhaseAmplitudeState Q N A →
  Fin Q → FiniteTargetSlot N → Coefficient
forwardAmplitude {Q = Q} A ψ k slot =
  sumCoefficients A
    (λ x →
      multiplyCoefficient A
        (normalisation A)
        (multiplyCoefficient A
          (phase A k x)
          (amplitude ψ x slot)))
    (allFin Q)

inverseAmplitude :
  ∀ {Coefficient Q N}
    (A : CyclicPhaseCoefficientAuthority Coefficient Q) →
  CyclicPhaseAmplitudeState Q N A →
  Fin Q → FiniteTargetSlot N → Coefficient
inverseAmplitude {Q = Q} A ψ x slot =
  sumCoefficients A
    (λ k →
      multiplyCoefficient A
        (normalisation A)
        (multiplyCoefficient A
          (inversePhase A x k)
          (amplitude ψ k slot)))
    (allFin Q)

cyclicPhaseForward :
  ∀ {Coefficient Q N}
    (A : CyclicPhaseCoefficientAuthority Coefficient Q) →
  CyclicPhaseAmplitudeState Q N A →
  CyclicPhaseAmplitudeState Q N A
cyclicPhaseForward A ψ =
  cyclicPhaseAmplitudeState
    (classicalTag ψ)
    (forwardAmplitude A ψ)

cyclicPhaseInverse :
  ∀ {Coefficient Q N}
    (A : CyclicPhaseCoefficientAuthority Coefficient Q) →
  CyclicPhaseAmplitudeState Q N A →
  CyclicPhaseAmplitudeState Q N A
cyclicPhaseInverse A ψ =
  cyclicPhaseAmplitudeState
    (classicalTag ψ)
    (inverseAmplitude A ψ)

forwardBasisCharacterSum :
  ∀ {Coefficient Q N}
    (qNonZero : B369.NonZero Q) →
    (nNonZero : B369.NonZero N) →
    (A : CyclicPhaseCoefficientAuthority Coefficient Q) →
  Fin Q → Fin N → CyclicPhaseAmplitudeState Q N A
forwardBasisCharacterSum qNonZero nNonZero A x y =
  cyclicPhaseForward A
    (basisAmplitude qNonZero nNonZero A x y)

record CyclicPhaseInversionAuthority
    {Coefficient : Set} {Q : Nat}
    (A : CyclicPhaseCoefficientAuthority Coefficient Q) : Set₁ where
  constructor cyclicPhaseInversionAuthority
  field
    inverseAfterForward :
      ∀ {N} (ψ : CyclicPhaseAmplitudeState Q N A) →
      cyclicPhaseInverse A (cyclicPhaseForward A ψ) ≡ ψ

    forwardAfterInverse :
      ∀ {N} (ψ : CyclicPhaseAmplitudeState Q N A) →
      cyclicPhaseForward A (cyclicPhaseInverse A ψ) ≡ ψ

open CyclicPhaseInversionAuthority public

cyclicPhaseFiniteFourierTransform :
  ∀ {Q N Coefficient}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (A : CyclicPhaseCoefficientAuthority Coefficient Q) →
  CyclicPhaseInversionAuthority A →
  QFT.FiniteFourierTransform
    (cyclicPhaseAmplitudeRegister qNonZero nNonZero A)
cyclicPhaseFiniteFourierTransform qNonZero nNonZero A I = record
  { fourier = cyclicPhaseForward A
  ; inverseFourier = cyclicPhaseInverse A
  ; inverseAfterFourier = inverseAfterForward I
  ; fourierAfterInverse = forwardAfterInverse I
  }

forwardRetainsTargetCoordinate :
  ∀ {Coefficient Q N}
    (A : CyclicPhaseCoefficientAuthority Coefficient Q) →
    (ψ : CyclicPhaseAmplitudeState Q N A) →
    (k : Fin Q) →
    (slot : FiniteTargetSlot N) →
  amplitude (cyclicPhaseForward A ψ) k slot
  ≡ forwardAmplitude A ψ k slot
forwardRetainsTargetCoordinate A ψ k slot = refl

record ShorCyclicPhaseAmplitudeQFTBoundary : Set where
  constructor shorCyclicPhaseAmplitudeQFTBoundary
  field
    exponentCarrierLiteralFinQ : Bool
    targetCarrierFiniteAndIndependent : Bool
    forwardKernelDefinitionallyCyclicCharacterSum : Bool
    inverseKernelDefinitionallyInverseCharacterSum : Bool
    targetCoordinateRetained : Bool
    concreteComplexCoefficientAuthorityInhabitedHere : Bool
    concreteRootOfUnityTableInhabitedHere : Bool
    inversionAuthorityInhabitedHere : Bool
    bornMeasurementInhabitedHere : Bool

canonicalShorCyclicPhaseAmplitudeQFTBoundary :
  ShorCyclicPhaseAmplitudeQFTBoundary
canonicalShorCyclicPhaseAmplitudeQFTBoundary =
  shorCyclicPhaseAmplitudeQFTBoundary
    true true true true true false false false false
