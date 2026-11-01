module DASHI.Interop.SLRProtectedPNFFleetReductionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)

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

-- A conflict witness contains both polarities for the *same typed fibre*.
-- Counts are observational inputs; this module does not infer a typed meet
-- from lexical resemblance.
record OppositePolarity (A : Set) : Set where
  constructor oppositePolarity
  field
    fibre : A
    positiveWitness : Nat
    negativeWitness : Nat

data Severity : Set where
  exact partial noTypedMeet contradiction : Severity

severityValue : Severity → Nat
severityValue exact = 0
severityValue partial = 1
severityValue noTypedMeet = 3
severityValue contradiction = 9

record ProtectedConflict (A : Set) : Set where
  constructor protectedConflict
  field
    opposite : OppositePolarity A
    grade : Severity
    gradeIsContradiction : grade ≡ contradiction
    protected : Protection A
    protectionIsFormal : protected ≡ formallyRequired (OppositePolarity.fibre opposite)

conflictProtection : ∀ {A} → OppositePolarity A → ProtectedConflict A
conflictProtection conflict =
  protectedConflict conflict contradiction refl
    (formallyRequired (OppositePolarity.fibre conflict)) refl

conflictSeverityNine : ∀ {A} (conflict : OppositePolarity A) →
  severityValue (ProtectedConflict.grade (conflictProtection conflict)) ≡ 9
conflictSeverityNine conflict = refl

conflictRetainedAtZeroBudget : ∀ {A} (conflict : OppositePolarity A) →
  retain (ProtectedConflict.protected (conflictProtection conflict)) ≡
    retainedFormal (OppositePolarity.fibre conflict)
conflictRetainedAtZeroBudget conflict = refl
