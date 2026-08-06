module DASHI.Physics.Foundations.FormalReceiptBoundaryExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Four distinct evidential levels.  A source declaration is not definitionally
-- equal to a kernel-checked theorem or a reproducible CI receipt.

data ArtefactLevel : Set where
  mathematicalIntention : ArtefactLevel
  formalSource : ArtefactLevel
  kernelChecked : ArtefactLevel
  reproducibleReceipt : ArtefactLevel

record ReceiptData : Set where
  constructor receiptData
  field
    level : ArtefactLevel
    sourcePresent : Bool
    kernelAccepted : Bool
    toolchainPinned : Bool
    sourceHashRecorded : Bool
    ciSucceeded : Bool

open ReceiptData public

sourceOnlyReceipt : ReceiptData
sourceOnlyReceipt =
  receiptData formalSource true false false false false

kernelReceipt : ReceiptData
kernelReceipt =
  receiptData kernelChecked true true false false false

reproducibleKernelReceipt : ReceiptData
reproducibleKernelReceipt =
  receiptData reproducibleReceipt true true true true true

sourceOnlyIsNotKernelReceipt : sourceOnlyReceipt ≡ kernelReceipt → ⊥
sourceOnlyIsNotKernelReceipt ()

kernelReceiptIsNotReproducibleReceipt :
  kernelReceipt ≡ reproducibleKernelReceipt → ⊥
kernelReceiptIsNotReproducibleReceipt ()

------------------------------------------------------------------------
-- Exact finite cyclic theorem.  The four stages are an automaton; no logical
-- consequence relation is inferred from the cycle alone.

data TlureyStage : Set where
  seedStage : TlureyStage
  counterStage : TlureyStage
  resonanceStage : TlureyStage
  overflowStage : TlureyStage

nextStage : TlureyStage → TlureyStage
nextStage seedStage = counterStage
nextStage counterStage = resonanceStage
nextStage resonanceStage = overflowStage
nextStage overflowStage = seedStage

nextStageFour : TlureyStage → TlureyStage
nextStageFour s = nextStage (nextStage (nextStage (nextStage s)))

fourCycleReturns : (s : TlureyStage) → nextStageFour s ≡ s
fourCycleReturns seedStage = refl
fourCycleReturns counterStage = refl
fourCycleReturns resonanceStage = refl
fourCycleReturns overflowStage = refl

------------------------------------------------------------------------
-- Finite threshold classifier.  Constructor names state the value's position
-- relative to the threshold, avoiding the reversed comparison terminology in
-- the attempted implementation.

data FiniteLevel : Set where
  belowThresholdLevel : FiniteLevel
  atThresholdLevel : FiniteLevel
  aboveThresholdLevel : FiniteLevel

data ThresholdState : Set where
  groundedState : ThresholdState
  plateauState : ThresholdState
  ascendedState : ThresholdState

classifyThreshold : FiniteLevel → ThresholdState
classifyThreshold belowThresholdLevel = groundedState
classifyThreshold atThresholdLevel = plateauState
classifyThreshold aboveThresholdLevel = ascendedState

belowClassifiesGrounded :
  classifyThreshold belowThresholdLevel ≡ groundedState
belowClassifiesGrounded = refl

atClassifiesPlateau :
  classifyThreshold atThresholdLevel ≡ plateauState
atClassifiesPlateau = refl

aboveClassifiesAscended :
  classifyThreshold aboveThresholdLevel ≡ ascendedState
aboveClassifiesAscended = refl

classificationIsTotal :
  (level : FiniteLevel) →
  (classifyThreshold level ≡ groundedState)
  ⊎
  ((classifyThreshold level ≡ plateauState)
    ⊎ (classifyThreshold level ≡ ascendedState))
classificationIsTotal belowThresholdLevel = inj₁ refl
classificationIsTotal atThresholdLevel = inj₂ (inj₁ refl)
classificationIsTotal aboveThresholdLevel = inj₂ (inj₂ refl)

record FormalReceiptBoundary : Set where
  constructor formalReceiptBoundary
  field
    theoremStatementAloneIsKernelReceipt : Bool
    theoremStatementAloneIsKernelReceiptIsFalse :
      theoremStatementAloneIsKernelReceipt ≡ false

    successfulUnrelatedRuntimeTestCompilesAgda : Bool
    successfulUnrelatedRuntimeTestCompilesAgdaIsFalse :
      successfulUnrelatedRuntimeTestCompilesAgda ≡ false

    finiteFourCycleIsAlreadyAParaconsistentLogic : Bool
    finiteFourCycleIsAlreadyAParaconsistentLogicIsFalse :
      finiteFourCycleIsAlreadyAParaconsistentLogic ≡ false

    finiteThresholdClassifierProvesPhysicalOverflowTheory : Bool
    finiteThresholdClassifierProvesPhysicalOverflowTheoryIsFalse :
      finiteThresholdClassifierProvesPhysicalOverflowTheory ≡ false

open FormalReceiptBoundary public

canonicalFormalReceiptBoundary : FormalReceiptBoundary
canonicalFormalReceiptBoundary =
  formalReceiptBoundary
    false refl
    false refl
    false refl
    false refl
