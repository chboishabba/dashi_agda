module DASHI.Moonshine.OggSSPK6FieldSelectingOperatorExact where

------------------------------------------------------------------------
-- POST-NO-GO K6 FIELD-SELECTING OPERATOR CONTRACT
--
-- The existing finite-Heisenberg/symplectic data admit swap01, while the
-- selected GF(3^6) multiplication does not.  Therefore a lawful recognition
-- source must contribute strictly richer structure on the SAME X6 carrier.
--
-- The original version of this owner exposed the least data needed from such a
-- source.  Cross-pollination with the Monster-3B ATLAS lane now pays the
-- acquisition part of that contract at exact-executable/same-object level:
--
--   * certified ATLAS 2.Suz:2 12-dimensional GF(3) matrices are vendored;
--   * a concrete source-word X6 compression is F3-linear, cyclic of degree 6,
--     and breaks the repository swap01 symmetry;
--   * OggSSPMonster3BSelectedGF729WeldExact records an explicit invertible Q
--     with Q T = M_beta Q for the already-selected GF(729) presentation;
--   * companion Lean source-writes the literal 6x6 intertwiner and Q inverse.
--
-- Full Monster action/orbit/stabilizer semantics remain separate.  In
-- particular, the acquisition closure below does not turn the compressed block
-- into a representation of the whole normalizer or manufacture physical
-- Monster semantics.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as F3
import DASHI.Moonshine.OggSSPHeisenbergSymplecticFieldNoGoExact as NoGo
import DASHI.Moonshine.OggSSPMonster3BSelectedGF729WeldExact as Weld

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

record K6FieldSelectingOperator : Set₁ where
  field
    operator : H.X6 → H.X6

    -- SAME additive F3^6 carrier, not a new six-dimensional proxy.
    preservesAdd :
      (x y : H.X6) →
      operator (F3.addX6 x y) ≡ F3.addX6 (operator x) (operator y)
    preservesNeg :
      (x : H.X6) →
      operator (F3.negX6 x) ≡ F3.negX6 (operator x)

    -- The source structure must distinguish the exact symmetry responsible
    -- for the current field non-canonicity theorem.
    swapBreakingWitness : H.X6
    breaksSwap01AtWitness :
      operator (NoGo.swap01X6 swapBreakingWitness)
      ≢ NoGo.swap01X6 (operator swapBreakingWitness)

    -- Independently checked algebra-generation receipt.  Degree/cyclic-span
    -- numerics are explicit, while any richer source-specific minimal-
    -- polynomial theorem is carried as an inhabited proposition.
    minimalPolynomialDegree : Nat
    minimalPolynomialDegreeIsSix : minimalPolynomialDegree ≡ 6
    cyclicSpanDimension : Nat
    cyclicSpanDimensionIsSix : cyclicSpanDimension ≡ 6
    FieldGeneratorReceipt : Set
    fieldGeneratorReceipt : FieldGeneratorReceipt

open K6FieldSelectingOperator public

fieldSelectorNotSwapEquivariant :
  (selector : K6FieldSelectingOperator) →
  ((x : H.X6) →
    operator selector (NoGo.swap01X6 x)
    ≡ NoGo.swap01X6 (operator selector x)) → ⊥
fieldSelectorNotSwapEquivariant selector allCommute =
  breaksSwap01AtWitness selector
    (allCommute (swapBreakingWitness selector))

------------------------------------------------------------------------
-- Current acquisition status.
--
-- The earlier target had `independentlyOwnedOperatorLocated = false`.  The
-- Monster-3B ATLAS compression now pays that exact seam.  `actualSameCarrier-
-- IntertwinerPaid` below means the explicit finite/executable conjugacy to the
-- selected GF(729) presentation is paid; it is NOT a claim that this Agda file
-- itself kernel-proves the 6x6 multiplication identity.  That stronger Agda
-- proof remains separately tracked in Weld.agdaKernelIntertwinerProofPaid.
------------------------------------------------------------------------

record K6FieldSelectorAcquisitionTarget : Set where
  constructor k6-field-selector-acquisition-target
  field
    minimalPolynomialDegree : Nat
    cyclicSpanDimension : Nat
    independentlyOwnedOperatorLocated : Bool
    actualSameCarrierIntertwinerPaid : Bool
    actionOrbitStabilizerRecognitionPaid : Bool

open K6FieldSelectorAcquisitionTarget public

canonicalAcquisitionTarget : K6FieldSelectorAcquisitionTarget
canonicalAcquisitionTarget =
  k6-field-selector-acquisition-target
    Weld.minimalPolynomialDegree
    Weld.cyclicSpanDimension
    true
    (Weld.selectedGF729PresentationWeldPaid Weld.canonicalBoundary)
    false

record K6FieldRecognitionPromotion : Set₁ where
  field
    selector : K6FieldSelectingOperator
    SameCarrierIntertwinerReceipt : Set
    sameCarrierIntertwiner : SameCarrierIntertwinerReceipt
    ActionOrbitStabilizerRecognitionReceipt : Set
    actionOrbitStabilizerRecognition : ActionOrbitStabilizerRecognitionReceipt

open K6FieldRecognitionPromotion public

record K6FieldSelectorCurrentBoundary : Set where
  constructor k6-field-selector-current-boundary
  field
    heisenbergOnlyFieldCanonicityNoGoPaid : Bool
    independentMonsterCompressionOperatorLocated : Bool
    swapBreakingReceiptPaidByExactProducer : Bool
    degreeSixCyclicReceiptPaidByExactProducer : Bool
    selectedGF729SameCarrierWeldPaidByExactProducer : Bool
    companionLeanLiteralMatrixIntertwinerSourceWritten : Bool
    companionLeanExactHeadKernelObserved : Bool
    agdaLiteralMatrixIntertwinerKernelPaid : Bool
    fullActionOrbitStabilizerRecognitionPaid : Bool
open K6FieldSelectorCurrentBoundary public

canonicalCurrentBoundary : K6FieldSelectorCurrentBoundary
canonicalCurrentBoundary =
  k6-field-selector-current-boundary
    true
    true
    (Weld.swap01BrokenByCompression Weld.canonicalBoundary)
    (Weld.degreeSixCompressionReceiptPaid Weld.canonicalBoundary)
    (Weld.selectedGF729PresentationWeldPaid Weld.canonicalBoundary)
    true
    false
    (Weld.agdaKernelIntertwinerProofPaid Weld.canonicalBoundary)
    false
