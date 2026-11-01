module DASHI.Physics.YangMills.BalabanCMP109Equation012PrimitiveActionsAreL13Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- DASHI CONTRIBUTION
--
-- Pointwise same-vector identification of every primitive action in the
-- printed equation-(0.12) derivative chain.  The purpose is not to prove one
-- terminal matrix coincidence after flattening; it is to ensure that the
-- actual derivative action of each printed primitive is the action consumed
-- by the semantic DAG and finally by the L13 finite matrix.
--
-- The primitive ordering is source average, crossing/relative product,
-- target reverse average, coarse inverse, principal log, finite average,
-- exponential and endpoint product.  Equality is proved on the SAME input
-- vector, so a later numerical bound cannot swap in a merely equinormed
-- derivative object.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record Equation012PrimitiveActionData
    (Direction Entry : Set) : Set₁ where
  field
    sourcePrinted sourceDAG sourceL13 : Direction → Entry
    crossingPrinted crossingDAG crossingL13 : Direction → Entry
    targetReversePrinted targetReverseDAG targetReverseL13 : Direction → Entry
    coarseInversePrinted coarseInverseDAG coarseInverseL13 : Direction → Entry
    principalLogPrinted principalLogDAG principalLogL13 : Direction → Entry
    finiteAveragePrinted finiteAverageDAG finiteAverageL13 : Direction → Entry
    exponentialPrinted exponentialDAG exponentialL13 : Direction → Entry
    endpointProductPrinted endpointProductDAG endpointProductL13 : Direction → Entry

    sourcePrintedIsDAG : ∀ h → sourcePrinted h ≡ sourceDAG h
    sourceDAGIsL13 : ∀ h → sourceDAG h ≡ sourceL13 h

    crossingPrintedIsDAG : ∀ h → crossingPrinted h ≡ crossingDAG h
    crossingDAGIsL13 : ∀ h → crossingDAG h ≡ crossingL13 h

    targetReversePrintedIsDAG : ∀ h → targetReversePrinted h ≡ targetReverseDAG h
    targetReverseDAGIsL13 : ∀ h → targetReverseDAG h ≡ targetReverseL13 h

    coarseInversePrintedIsDAG : ∀ h → coarseInversePrinted h ≡ coarseInverseDAG h
    coarseInverseDAGIsL13 : ∀ h → coarseInverseDAG h ≡ coarseInverseL13 h

    principalLogPrintedIsDAG : ∀ h → principalLogPrinted h ≡ principalLogDAG h
    principalLogDAGIsL13 : ∀ h → principalLogDAG h ≡ principalLogL13 h

    finiteAveragePrintedIsDAG : ∀ h → finiteAveragePrinted h ≡ finiteAverageDAG h
    finiteAverageDAGIsL13 : ∀ h → finiteAverageDAG h ≡ finiteAverageL13 h

    exponentialPrintedIsDAG : ∀ h → exponentialPrinted h ≡ exponentialDAG h
    exponentialDAGIsL13 : ∀ h → exponentialDAG h ≡ exponentialL13 h

    endpointProductPrintedIsDAG : ∀ h → endpointProductPrinted h ≡ endpointProductDAG h
    endpointProductDAGIsL13 : ∀ h → endpointProductDAG h ≡ endpointProductL13 h

open Equation012PrimitiveActionData public

sourcePrimitiveActionIsL13 :
  ∀ {Direction Entry} (actions : Equation012PrimitiveActionData Direction Entry) h →
  sourcePrinted actions h ≡ sourceL13 actions h
sourcePrimitiveActionIsL13 actions h =
  trans (sourcePrintedIsDAG actions h) (sourceDAGIsL13 actions h)

crossingPrimitiveActionIsL13 :
  ∀ {Direction Entry} (actions : Equation012PrimitiveActionData Direction Entry) h →
  crossingPrinted actions h ≡ crossingL13 actions h
crossingPrimitiveActionIsL13 actions h =
  trans (crossingPrintedIsDAG actions h) (crossingDAGIsL13 actions h)

targetReversePrimitiveActionIsL13 :
  ∀ {Direction Entry} (actions : Equation012PrimitiveActionData Direction Entry) h →
  targetReversePrinted actions h ≡ targetReverseL13 actions h
targetReversePrimitiveActionIsL13 actions h =
  trans (targetReversePrintedIsDAG actions h) (targetReverseDAGIsL13 actions h)

coarseInversePrimitiveActionIsL13 :
  ∀ {Direction Entry} (actions : Equation012PrimitiveActionData Direction Entry) h →
  coarseInversePrinted actions h ≡ coarseInverseL13 actions h
coarseInversePrimitiveActionIsL13 actions h =
  trans (coarseInversePrintedIsDAG actions h) (coarseInverseDAGIsL13 actions h)

principalLogPrimitiveActionIsL13 :
  ∀ {Direction Entry} (actions : Equation012PrimitiveActionData Direction Entry) h →
  principalLogPrinted actions h ≡ principalLogL13 actions h
principalLogPrimitiveActionIsL13 actions h =
  trans (principalLogPrintedIsDAG actions h) (principalLogDAGIsL13 actions h)

finiteAveragePrimitiveActionIsL13 :
  ∀ {Direction Entry} (actions : Equation012PrimitiveActionData Direction Entry) h →
  finiteAveragePrinted actions h ≡ finiteAverageL13 actions h
finiteAveragePrimitiveActionIsL13 actions h =
  trans (finiteAveragePrintedIsDAG actions h) (finiteAverageDAGIsL13 actions h)

exponentialPrimitiveActionIsL13 :
  ∀ {Direction Entry} (actions : Equation012PrimitiveActionData Direction Entry) h →
  exponentialPrinted actions h ≡ exponentialL13 actions h
exponentialPrimitiveActionIsL13 actions h =
  trans (exponentialPrintedIsDAG actions h) (exponentialDAGIsL13 actions h)

endpointProductPrimitiveActionIsL13 :
  ∀ {Direction Entry} (actions : Equation012PrimitiveActionData Direction Entry) h →
  endpointProductPrinted actions h ≡ endpointProductL13 actions h
endpointProductPrimitiveActionIsL13 actions h =
  trans (endpointProductPrintedIsDAG actions h) (endpointProductDAGIsL13 actions h)

record Equation012PrimitiveActionBundle
    (Direction Entry : Set) : Set₁ where
  field
    actions : Equation012PrimitiveActionData Direction Entry

open Equation012PrimitiveActionBundle public

printedEquation012DerivativeActionIsL13 :
  ∀ {Direction Entry}
    (bundle : Equation012PrimitiveActionBundle Direction Entry) h →
  endpointProductPrinted (actions bundle) h
  ≡ endpointProductL13 (actions bundle) h
printedEquation012DerivativeActionIsL13 bundle h =
  endpointProductPrimitiveActionIsL13 (actions bundle) h

cmp109Equation012PrimitivePointwiseIdentificationLevel : ProofLevel
cmp109Equation012PrimitivePointwiseIdentificationLevel = machineChecked

cmp109Equation012PrintedDerivativeActionIsL13Level : ProofLevel
cmp109Equation012PrintedDerivativeActionIsL13Level = machineChecked
