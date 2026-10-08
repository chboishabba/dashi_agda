module DASHI.Moonshine.OggSSPK6FieldSelectingOperatorExact where

------------------------------------------------------------------------
-- POST-NO-GO K6 FIELD-SELECTING OPERATOR CONTRACT
--
-- The existing finite-Heisenberg/symplectic data admit swap01, while the
-- selected GF(3^6) multiplication does not.  Therefore a lawful recognition
-- source must contribute strictly richer structure on the SAME X6 carrier.
--
-- This owner makes that max-cut exact.  It does not fabricate the missing
-- source operator: it states the least data that would close the acquisition
-- seam and proves that any inhabitant necessarily defeats swap01 equivariance.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as F3
import DASHI.Moonshine.OggSSPHeisenbergSymplecticFieldNoGoExact as NoGo

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

record K6FieldSelectingOperator : Set where
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

    -- Independently checked algebra-generation receipt.  These fields are
    -- deliberately source-facing rather than inferred from cardinality.
    minimalPolynomialDegree : Nat
    minimalPolynomialDegreeIsSix : minimalPolynomialDegree ≡ 6
    cyclicSpanDimension : Nat
    cyclicSpanDimensionIsSix : cyclicSpanDimension ≡ 6

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
-- Current acquisition target.  The numerical requirements are fixed; the
-- independently owned operator itself remains the live external theorem.
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
  k6-field-selector-acquisition-target 6 6 false false false

record K6FieldRecognitionPromotion : Set where
  field
    selector : K6FieldSelectingOperator
    sameCarrierIntertwiner : Set
    actionOrbitStabilizerRecognition : Set

open K6FieldRecognitionPromotion public
