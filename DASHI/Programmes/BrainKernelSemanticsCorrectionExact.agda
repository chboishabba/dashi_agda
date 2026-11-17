module DASHI.Programmes.BrainKernelSemanticsCorrectionExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Corrected semantic owner for the dashiBRAIN kernel description.
--
-- A local ternary update of the form sign(A s) is a deterministic local kernel.
-- It is NOT definitionally an involution, idempotent projection, contraction,
-- or defect-decreasing map.  Those properties require independent receipts.
-- Kernel closure is therefore represented only as the fixed-point statement.
------------------------------------------------------------------------

record BrainKernelSemantics (State : Set) : Set₁ where
  constructor brainKernelSemantics
  field
    step : State → State
    defect : State → Nat

    localityReceipt : Set
    determinismReceipt : Set
    symmetryEquivarianceReceipt : Set

    zeroDefectImpliesFixed :
      (state : State) → defect state ≡ 0 → step state ≡ state

open BrainKernelSemantics public

KernelClosed :
  ∀ {State : Set} →
  BrainKernelSemantics State → State → Set
KernelClosed semantics state = step semantics state ≡ state

zeroDefectClosesKernel :
  ∀ {State : Set}
    (semantics : BrainKernelSemantics State)
    (state : State) →
  defect semantics state ≡ 0 →
  KernelClosed semantics state
zeroDefectClosesKernel semantics state zero =
  zeroDefectImpliesFixed semantics state zero

record BrainKernelOptionalStrengthening (State : Set)
    (semantics : BrainKernelSemantics State) : Set₁ where
  constructor brainKernelOptionalStrengthening
  field
    idempotentReceipt :
      (state : State) →
      step semantics (step semantics state) ≡ step semantics state

    defectNonincreaseReceipt :
      Set

open BrainKernelOptionalStrengthening public

------------------------------------------------------------------------
-- Boundary: the optional strengthening cannot be inferred from the formula or
-- from the existence of low-defect states.
------------------------------------------------------------------------

record BrainKernelCorrectionBoundary : Set where
  constructor brainKernelCorrectionBoundary
  field
    localSignKernelIsAutomaticallyIdempotent : Bool
    localSignKernelIsAutomaticallyIdempotentIsFalse :
      localSignKernelIsAutomaticallyIdempotent ≡ false

    lowDefectIsDefinitionallyKernelClosure : Bool
    lowDefectIsDefinitionallyKernelClosureIsFalse :
      lowDefectIsDefinitionallyKernelClosure ≡ false

    shortCycleContradictsKernelSemantics : Bool
    shortCycleContradictsKernelSemanticsIsFalse :
      shortCycleContradictsKernelSemantics ≡ false

    zeroDefectMayCertifyFixedPointWithReceipt : Bool
    zeroDefectMayCertifyFixedPointWithReceiptIsTrue :
      zeroDefectMayCertifyFixedPointWithReceipt ≡ true

canonicalBrainKernelCorrectionBoundary : BrainKernelCorrectionBoundary
canonicalBrainKernelCorrectionBoundary =
  brainKernelCorrectionBoundary
    false refl
    false refl
    false refl
    true refl
