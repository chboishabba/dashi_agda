module DASHI.Physics.Closure.ScaleGraphBarrierAlgebraProofReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.DangerScaleEdgeConservationReceipt as Edge
import DASHI.Physics.Closure.ScaleGraphBarrierTargetReceipt as Barrier
import DASHI.Physics.Closure.StrictMarginImpliesAbsorptionReceipt as L0
import DASHI.Physics.Closure.UniversalScaleGraphBarrierTargetReceipt
  as Universal

------------------------------------------------------------------------
-- Receipt-level algebra for the scale-graph barrier.
--
-- This module records the abstract ordered-margin calculation used by the
-- scale-graph target.  It is deliberately separate from the analytic lane
-- edge laws: NS, YM, and Gate3 still have to supply their own transfer
-- estimates before the barrier target can be consumed as a theorem.

data ScaleGraphBarrierAlgebraStatus : Set where
  scaleGraphBarrierAlgebraRecorded_failClosed :
    ScaleGraphBarrierAlgebraStatus

data AlgebraQuantity : Set where
  residualRate :
    AlgebraQuantity

  productionTerm :
    AlgebraQuantity

  incomingLeakage :
    AlgebraQuantity

  absorptionTerm :
    AlgebraQuantity

  productionSlope :
    AlgebraQuantity

  leakageSlope :
    AlgebraQuantity

canonicalAlgebraQuantities : List AlgebraQuantity
canonicalAlgebraQuantities =
  residualRate
  ∷ productionTerm
  ∷ incomingLeakage
  ∷ absorptionTerm
  ∷ productionSlope
  ∷ leakageSlope
  ∷ []

data AlgebraPremise : Set where
  residualRateBoundedByProductionPlusIncomingMinusAbsorption :
    AlgebraPremise

  productionBoundedByThetaAbsorption :
    AlgebraPremise

  incomingBoundedByEpsilonAbsorption :
    AlgebraPremise

  thetaPlusEpsilonStrictlyBelowOne :
    AlgebraPremise

  absorptionStrictlyPositive :
    AlgebraPremise

canonicalAlgebraPremises : List AlgebraPremise
canonicalAlgebraPremises =
  residualRateBoundedByProductionPlusIncomingMinusAbsorption
  ∷ productionBoundedByThetaAbsorption
  ∷ incomingBoundedByEpsilonAbsorption
  ∷ thetaPlusEpsilonStrictlyBelowOne
  ∷ absorptionStrictlyPositive
  ∷ []

data AlgebraStep : Set where
  substituteProductionAndIncomingBounds :
    AlgebraStep

  factorAbsorptionCoefficient :
    AlgebraStep

  rewriteCoefficientAsNegativeMargin :
    AlgebraStep

  useStrictPositiveMarginAndAbsorption :
    AlgebraStep

  concludeResidualRateStrictlyNegative :
    AlgebraStep

canonicalAlgebraSteps : List AlgebraStep
canonicalAlgebraSteps =
  substituteProductionAndIncomingBounds
  ∷ factorAbsorptionCoefficient
  ∷ rewriteCoefficientAsNegativeMargin
  ∷ useStrictPositiveMarginAndAbsorption
  ∷ concludeResidualRateStrictlyNegative
  ∷ []

data AlgebraConclusion : Set where
  residualRateBoundedByNegativeNetAbsorber :
    AlgebraConclusion

  residualRateStrictlyNegative :
    AlgebraConclusion

  residualEnvelopeDecreases :
    AlgebraConclusion

canonicalAlgebraConclusions : List AlgebraConclusion
canonicalAlgebraConclusions =
  residualRateBoundedByNegativeNetAbsorber
  ∷ residualRateStrictlyNegative
  ∷ residualEnvelopeDecreases
  ∷ []

data AlgebraLane : Set where
  algebraLaneNS :
    AlgebraLane

  algebraLaneYM :
    AlgebraLane

  algebraLaneGate3 :
    AlgebraLane

canonicalAlgebraLanes : List AlgebraLane
canonicalAlgebraLanes =
  algebraLaneNS
  ∷ algebraLaneYM
  ∷ algebraLaneGate3
  ∷ []

data LaneEdgeLawObligation : Set where
  nsAdjacentShellTransferLaw :
    LaneEdgeLawObligation

  ymBlockSpinRecurrenceLaw :
    LaneEdgeLawObligation

  gate3RefinementDefectAccountingLaw :
    LaneEdgeLawObligation

canonicalLaneEdgeLawObligation :
  AlgebraLane →
  LaneEdgeLawObligation
canonicalLaneEdgeLawObligation algebraLaneNS =
  nsAdjacentShellTransferLaw
canonicalLaneEdgeLawObligation algebraLaneYM =
  ymBlockSpinRecurrenceLaw
canonicalLaneEdgeLawObligation algebraLaneGate3 =
  gate3RefinementDefectAccountingLaw

record LaneEdgeLawRow : Set where
  field
    lane :
      AlgebraLane

    obligation :
      LaneEdgeLawObligation

    obligationIsCanonical :
      obligation ≡ canonicalLaneEdgeLawObligation lane

    edgeLawClosed :
      Bool

    edgeLawClosedIsFalse :
      edgeLawClosed ≡ false

open LaneEdgeLawRow public

rowFor : AlgebraLane → LaneEdgeLawRow
rowFor lane =
  record
    { lane =
        lane
    ; obligation =
        canonicalLaneEdgeLawObligation lane
    ; obligationIsCanonical =
        refl
    ; edgeLawClosed =
        false
    ; edgeLawClosedIsFalse =
        refl
    }

canonicalLaneEdgeLawRows : List LaneEdgeLawRow
canonicalLaneEdgeLawRows =
  rowFor algebraLaneNS
  ∷ rowFor algebraLaneYM
  ∷ rowFor algebraLaneGate3
  ∷ []

data AlgebraNonClaim : Set where
  noLaneEdgeLawClosedHere :
    AlgebraNonClaim

  noComparisonPrincipleClosedHere :
    AlgebraNonClaim

  noDomainClosurePromotedHere :
    AlgebraNonClaim

  noClayPromotionHere :
    AlgebraNonClaim

canonicalAlgebraNonClaims : List AlgebraNonClaim
canonicalAlgebraNonClaims =
  noLaneEdgeLawClosedHere
  ∷ noComparisonPrincipleClosedHere
  ∷ noDomainClosurePromotedHere
  ∷ noClayPromotionHere
  ∷ []

data ScaleGraphBarrierAlgebraPromotion : Set where

scaleGraphBarrierAlgebraPromotionImpossibleHere :
  ScaleGraphBarrierAlgebraPromotion →
  ⊥
scaleGraphBarrierAlgebraPromotionImpossibleHere ()

algebraLemmaStatement : String
algebraLemmaStatement =
  "R' <= P + I - A, P <= theta*A, I <= epsilon*A, theta+epsilon<1, A>0 => R' <= -(1-theta-epsilon)*A < 0, hence the residual decreases."

laneObligationStatement : String
laneObligationStatement =
  "NS adjacent-shell transfer, YM block-spin recurrence, and Gate3 refinement-defect accounting remain external lane edge laws."

record ScaleGraphBarrierAlgebraProofReceipt : Setω where
  field
    status :
      ScaleGraphBarrierAlgebraStatus

    statusIsFailClosed :
      status ≡ scaleGraphBarrierAlgebraRecorded_failClosed

    l0Receipt :
      L0.StrictMarginImpliesAbsorptionReceipt

    l0NoClay :
      L0.StrictMarginImpliesAbsorptionReceipt.clayPromotion l0Receipt
      ≡
      false

    barrierReceipt :
      Barrier.ScaleGraphBarrierTargetReceipt

    barrierStillTarget :
      Barrier.comparisonPrincipleProvedHere barrierReceipt ≡ false

    barrierNoClay :
      Barrier.clayPromotion barrierReceipt ≡ false

    universalReceipt :
      Universal.UniversalScaleGraphBarrierTargetReceipt

    universalStillTarget :
      Universal.barrierTheoremProvedHere universalReceipt ≡ false

    universalNoClay :
      Universal.clayPromotionMade universalReceipt ≡ false

    edgeReceipt :
      Edge.DangerScaleEdgeConservationReceipt

    edgeConservationStillExternal :
      Edge.edgeConservationProvedHere edgeReceipt ≡ false

    edgeReceiptNoClay :
      Edge.clayPromotion edgeReceipt ≡ false

    quantities :
      List AlgebraQuantity

    quantitiesAreCanonical :
      quantities ≡ canonicalAlgebraQuantities

    premises :
      List AlgebraPremise

    premisesAreCanonical :
      premises ≡ canonicalAlgebraPremises

    steps :
      List AlgebraStep

    stepsAreCanonical :
      steps ≡ canonicalAlgebraSteps

    conclusions :
      List AlgebraConclusion

    conclusionsAreCanonical :
      conclusions ≡ canonicalAlgebraConclusions

    lanes :
      List AlgebraLane

    lanesAreCanonical :
      lanes ≡ canonicalAlgebraLanes

    laneRows :
      List LaneEdgeLawRow

    laneRowsAreCanonical :
      laneRows ≡ canonicalLaneEdgeLawRows

    nonClaims :
      List AlgebraNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalAlgebraNonClaims

    algebraLemmaRecorded :
      Bool

    algebraLemmaRecordedIsTrue :
      algebraLemmaRecorded ≡ true

    orderedRingCarrierSuppliedHere :
      Bool

    orderedRingCarrierSuppliedHereIsFalse :
      orderedRingCarrierSuppliedHere ≡ false

    laneEdgeLawsClosedHere :
      Bool

    laneEdgeLawsClosedHereIsFalse :
      laneEdgeLawsClosedHere ≡ false

    comparisonPrincipleProvedHere :
      Bool

    comparisonPrincipleProvedHereIsFalse :
      comparisonPrincipleProvedHere ≡ false

    provesNSRegularity :
      Bool

    provesNSRegularityIsFalse :
      provesNSRegularity ≡ false

    provesYMMassGap :
      Bool

    provesYMMassGapIsFalse :
      provesYMMassGap ≡ false

    provesGate3ContinuumLift :
      Bool

    provesGate3ContinuumLiftIsFalse :
      provesGate3ContinuumLift ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    lemmaStatement :
      String

    lemmaStatementIsCanonical :
      lemmaStatement ≡ algebraLemmaStatement

    laneStatement :
      String

    laneStatementIsCanonical :
      laneStatement ≡ laneObligationStatement

    promotions :
      List ScaleGraphBarrierAlgebraPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      ScaleGraphBarrierAlgebraPromotion →
      ⊥

open ScaleGraphBarrierAlgebraProofReceipt public

canonicalScaleGraphBarrierAlgebraProofReceipt :
  ScaleGraphBarrierAlgebraProofReceipt
canonicalScaleGraphBarrierAlgebraProofReceipt =
  record
    { status =
        scaleGraphBarrierAlgebraRecorded_failClosed
    ; statusIsFailClosed =
        refl
    ; l0Receipt =
        L0.canonicalStrictMarginImpliesAbsorptionReceipt
    ; l0NoClay =
        refl
    ; barrierReceipt =
        Barrier.canonicalScaleGraphBarrierTargetReceipt
    ; barrierStillTarget =
        refl
    ; barrierNoClay =
        refl
    ; universalReceipt =
        Universal.canonicalUniversalScaleGraphBarrierTargetReceipt
    ; universalStillTarget =
        refl
    ; universalNoClay =
        refl
    ; edgeReceipt =
        Edge.canonicalDangerScaleEdgeConservationReceipt
    ; edgeConservationStillExternal =
        refl
    ; edgeReceiptNoClay =
        refl
    ; quantities =
        canonicalAlgebraQuantities
    ; quantitiesAreCanonical =
        refl
    ; premises =
        canonicalAlgebraPremises
    ; premisesAreCanonical =
        refl
    ; steps =
        canonicalAlgebraSteps
    ; stepsAreCanonical =
        refl
    ; conclusions =
        canonicalAlgebraConclusions
    ; conclusionsAreCanonical =
        refl
    ; lanes =
        canonicalAlgebraLanes
    ; lanesAreCanonical =
        refl
    ; laneRows =
        canonicalLaneEdgeLawRows
    ; laneRowsAreCanonical =
        refl
    ; nonClaims =
        canonicalAlgebraNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; algebraLemmaRecorded =
        true
    ; algebraLemmaRecordedIsTrue =
        refl
    ; orderedRingCarrierSuppliedHere =
        false
    ; orderedRingCarrierSuppliedHereIsFalse =
        refl
    ; laneEdgeLawsClosedHere =
        false
    ; laneEdgeLawsClosedHereIsFalse =
        refl
    ; comparisonPrincipleProvedHere =
        false
    ; comparisonPrincipleProvedHereIsFalse =
        refl
    ; provesNSRegularity =
        false
    ; provesNSRegularityIsFalse =
        refl
    ; provesYMMassGap =
        false
    ; provesYMMassGapIsFalse =
        refl
    ; provesGate3ContinuumLift =
        false
    ; provesGate3ContinuumLiftIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; lemmaStatement =
        algebraLemmaStatement
    ; lemmaStatementIsCanonical =
        refl
    ; laneStatement =
        laneObligationStatement
    ; laneStatementIsCanonical =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        scaleGraphBarrierAlgebraPromotionImpossibleHere
    }

canonicalScaleGraphBarrierAlgebraRecorded :
  algebraLemmaRecorded canonicalScaleGraphBarrierAlgebraProofReceipt
  ≡
  true
canonicalScaleGraphBarrierAlgebraRecorded =
  refl

canonicalScaleGraphBarrierAlgebraNoLaneEdgeLaw :
  laneEdgeLawsClosedHere canonicalScaleGraphBarrierAlgebraProofReceipt
  ≡
  false
canonicalScaleGraphBarrierAlgebraNoLaneEdgeLaw =
  refl

canonicalScaleGraphBarrierAlgebraNoClay :
  clayPromotion canonicalScaleGraphBarrierAlgebraProofReceipt
  ≡
  false
canonicalScaleGraphBarrierAlgebraNoClay =
  refl
