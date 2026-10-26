module DASHI.Interop.SLRProtectedPNFFleetReductionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)

-- Classification is on raw PNF1 *slot records*, not grouped frames.
-- A repair demand is the only permissible destination for an invalidated
-- slot that carries an exact protected obligation witness.
record SlotPartition : Set where
  constructor slotPartition
  field
    invalidSlots : Nat
    repairDemandSlots : Nat
    admittedFrameSlots : Nat
    rawSlots : Nat
    partitionExact : rawSlots ≡
      invalidSlots + (repairDemandSlots + admittedFrameSlots)

open SlotPartition public

-- A protected witness cannot be eliminated by statistical selection.
-- The witness must come from the producer's exact formal/review receipt.
data Protection (A : Set) : Set where
  spectral : A → Protection A
  formallyRequired : A → Protection A
  reviewed : A → Protection A

data Retained (A : Set) : Set where
  retainedSpectral : A → Retained A
  retainedFormal : A → Retained A
  retainedReviewed : A → Retained A

retain : ∀ {A} → Protection A → Retained A
retain (spectral x) = retainedSpectral x
retain (formallyRequired x) = retainedFormal x
retain (reviewed x) = retainedReviewed x

formalSingletonRetained : ∀ {A} (x : A) →
  retain (formallyRequired x) ≡ retainedFormal x
formalSingletonRetained x = refl

reviewedSingletonRetained : ∀ {A} (x : A) →
  retain (reviewed x) ≡ retainedReviewed x
reviewedSingletonRetained x = refl

-- Distinct evidence classes; spectral admission is not kernel certification.
data KnowledgeStatus : Set where
  admittedCore spectralMotif kernelCertified : KnowledgeStatus

data KernelEvidence : Set where
  independentlyChecked : KernelEvidence

certify : KernelEvidence → KnowledgeStatus
certify independentlyChecked = kernelCertified

-- These impossibility results prevent constructors from being conflated.
spectralIsNotCertified : spectralMotif ≡ kernelCertified → ⊥
spectralIsNotCertified ()

admittedIsNotCertified : admittedCore ≡ kernelCertified → ⊥
admittedIsNotCertified ()

open import Data.Empty using (⊥)
