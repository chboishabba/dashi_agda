module DASHI.Reasoning.LILACubeEmpiricalSameObjectReceiptExact where

------------------------------------------------------------------------
-- LILA -> CONCRETE CUBE EMPIRICAL SAME-OBJECT RECEIPT
--
-- The current LILA/E8 programme already owns geometric-prior, action-fit,
-- held-out-word and consumer-relative experiment interfaces.  Its live ledger
-- still marks actual LILA trajectory/action fitting as unpaid.  This owner does
-- not manufacture model data.  It states exactly what an actual checkpoint /
-- trajectory tranche must inhabit before the cube/IIT geometry can be called a
-- same-object model result.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.IITCubeConcreteTorusImageExact as Cube

record LILACubeEmpiricalSameObjectReceipt
  (Hidden Output : Set) : Set where
  constructor lila-cube-empirical-same-object-receipt
  field
    -- Actual model dynamics and actual selected cube dynamics.
    hiddenNext : Hidden → Hidden
    cubeNext : Cube.CubeFaces → Cube.CubeFaces

    -- Learned/measured representation map on the actual hidden carrier.
    hiddenToCube : Hidden → Cube.CubeFaces

    -- Same-object dynamics payment: project after update = update after project.
    transitionIntertwines :
      (h : Hidden) →
      hiddenToCube (hiddenNext h) ≡ cubeNext (hiddenToCube h)

    -- The cube image must land in the concrete reachable graph, not merely in
    -- an arbitrary 27-state carrier with matching cardinality.
    projectedStateIsReachable :
      (h : Hidden) → Cube.GraphLaw (hiddenToCube h)

    -- Consumer-relative payment.  Geometry is useful only if the declared
    -- downstream quantity actually factors through the selected representation.
    hiddenConsumer : Hidden → Output
    cubeConsumer : Cube.CubeFaces → Output
    consumerFactorsThroughCube :
      (h : Hidden) → hiddenConsumer h ≡ cubeConsumer (hiddenToCube h)

open LILACubeEmpiricalSameObjectReceipt public

record LILACubeEmpiricalPaymentBoundary : Set where
  constructor lila-cube-empirical-payment-boundary
  field
    receiptTypePresent : Bool
    actualHiddenTrajectoryArtifactLocatedOnIITBranch : Bool
    actualCheckpointProjectionInhabitsReceipt : Bool
    heldOutConsumerSameObjectPaymentInhabited : Bool
    cardinalityOrCodebookFitAloneCountsAsPayment : Bool
open LILACubeEmpiricalPaymentBoundary public

canonicalLILACubeEmpiricalPaymentBoundary : LILACubeEmpiricalPaymentBoundary
canonicalLILACubeEmpiricalPaymentBoundary =
  lila-cube-empirical-payment-boundary
    true
    false
    false
    false
    false
