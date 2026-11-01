module DASHI.Physics.Closure.NSTriadKNClasswiseSignedEnvelopeAssembly where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; _+_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as Nat

import DASHI.Physics.Closure.NSTriadKNPhysicalStage3Allocation as Allocation

------------------------------------------------------------------------
-- Classwise assembly for the magnitude of the exact signed coefficient.
--
-- The local envelope is not itself assumed to be the Navier--Stokes
-- coefficient.  It majorizes a separately supplied magnitude of the exact
-- signed coefficient.  Summation and constant bookkeeping are derived here.
------------------------------------------------------------------------

sumNat : List Nat → Nat
sumNat [] = zero
sumNat (x ∷ xs) = x + sumNat xs

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

sumPointwiseBounds :
  ∀ {A : Set}
    (actual envelope : A → Nat) →
  ((x : A) → actual x ≤ envelope x) →
  (xs : List A) →
  sumNat (mapList actual xs) ≤ sumNat (mapList envelope xs)
sumPointwiseBounds actual envelope local [] = Nat.≤-refl
sumPointwiseBounds actual envelope local (x ∷ xs) =
  Nat.+-mono-≤
    (local x)
    (sumPointwiseBounds actual envelope local xs)

record ClasswiseEnvelopeInputs (PhysicalIncidence : Set) : Set₁ where
  constructor classwise-envelope-inputs
  field
    classify : PhysicalIncidence → Allocation.Stage3Class

    exactSignedMagnitude : PhysicalIncidence → Nat

    forcedTailEnvelope transitionEnvelope adversarialEnvelope residualEnvelope :
      PhysicalIncidence → Nat

    forcedTailBound :
      (τ : PhysicalIncidence) →
      classify τ ≡ Allocation.forcedTail →
      exactSignedMagnitude τ ≤ forcedTailEnvelope τ

    transitionBound :
      (τ : PhysicalIncidence) →
      classify τ ≡ Allocation.transition →
      exactSignedMagnitude τ ≤ transitionEnvelope τ

    adversarialBound :
      (τ : PhysicalIncidence) →
      classify τ ≡ Allocation.adversarial →
      exactSignedMagnitude τ ≤ adversarialEnvelope τ

    residualBound :
      (τ : PhysicalIncidence) →
      classify τ ≡ Allocation.residual →
      exactSignedMagnitude τ ≤ residualEnvelope τ

open ClasswiseEnvelopeInputs public

selectedEnvelope :
  ∀ {PhysicalIncidence} →
  ClasswiseEnvelopeInputs PhysicalIncidence →
  PhysicalIncidence → Nat
selectedEnvelope inputs τ with classify inputs τ
... | Allocation.forcedTail = forcedTailEnvelope inputs τ
... | Allocation.transition = transitionEnvelope inputs τ
... | Allocation.adversarial = adversarialEnvelope inputs τ
... | Allocation.residual = residualEnvelope inputs τ

selectedEnvelopeBoundsExactMagnitude :
  ∀ {PhysicalIncidence}
    (inputs : ClasswiseEnvelopeInputs PhysicalIncidence)
    (τ : PhysicalIncidence) →
  exactSignedMagnitude inputs τ ≤ selectedEnvelope inputs τ
selectedEnvelopeBoundsExactMagnitude inputs τ
  with classify inputs τ
... | Allocation.forcedTail =
  forcedTailBound inputs τ refl
... | Allocation.transition =
  transitionBound inputs τ refl
... | Allocation.adversarial =
  adversarialBound inputs τ refl
... | Allocation.residual =
  residualBound inputs τ refl

classwiseEnvelopeSumBound :
  ∀ {PhysicalIncidence}
    (inputs : ClasswiseEnvelopeInputs PhysicalIncidence)
    (incidences : List PhysicalIncidence) →
  sumNat (mapList (exactSignedMagnitude inputs) incidences)
  ≤
  sumNat (mapList (selectedEnvelope inputs) incidences)
classwiseEnvelopeSumBound inputs =
  sumPointwiseBounds
    (exactSignedMagnitude inputs)
    (selectedEnvelope inputs)
    (selectedEnvelopeBoundsExactMagnitude inputs)

------------------------------------------------------------------------
-- Uniform Schur endpoint.  This record does not contain local coefficient
-- estimates; it consumes the classwise sums derived above.
------------------------------------------------------------------------

record UniformClasswiseSchurCertificate : Set₁ where
  constructor uniform-classwise-schur-certificate
  field
    Cutoff Index : Set

    scaleSquare : Cutoff → Nat

    forcedTailRow transitionRow adversarialRow residualRow :
      Cutoff → Index → Nat

    forcedTailConstant transitionConstant adversarialConstant residualConstant :
      Nat

    forcedTailUniform :
      ∀ N i →
      scaleSquare N * forcedTailRow N i ≤ forcedTailConstant

    transitionUniform :
      ∀ N i →
      scaleSquare N * transitionRow N i ≤ transitionConstant

    adversarialUniform :
      ∀ N i →
      scaleSquare N * adversarialRow N i ≤ adversarialConstant

    residualUniform :
      ∀ N i →
      scaleSquare N * residualRow N i ≤ residualConstant

open UniformClasswiseSchurCertificate public

totalErrorConstant : UniformClasswiseSchurCertificate → Nat
totalErrorConstant certificate =
  forcedTailConstant certificate
  + transitionConstant certificate
  + adversarialConstant certificate
  + residualConstant certificate

record StrictGapFromClasswiseSchur
    (certificate : UniformClasswiseSchurCertificate) : Set where
  constructor strict-gap-from-classwise-schur
  field
    baseConstant : Nat
    strictGap : totalErrorConstant certificate < baseConstant

open StrictGapFromClasswiseSchur public

classwiseEnvelopeAssemblyImplemented : Bool
classwiseEnvelopeAssemblyImplemented = true

classwiseEnvelopeAssemblyImplementedIsTrue :
  classwiseEnvelopeAssemblyImplemented ≡ true
classwiseEnvelopeAssemblyImplementedIsTrue = refl

concreteUniformClassEnvelopesClosed : Bool
concreteUniformClassEnvelopesClosed = false

concreteUniformClassEnvelopesClosedIsFalse :
  concreteUniformClassEnvelopesClosed ≡ false
concreteUniformClassEnvelopesClosedIsFalse = refl
