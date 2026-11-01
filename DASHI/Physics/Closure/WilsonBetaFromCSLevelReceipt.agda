module DASHI.Physics.Closure.WilsonBetaFromCSLevelReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.CSLevelFlowFullReceipt as CS

------------------------------------------------------------------------
-- Corrected Wilson-beta audit from Chern-Simons level data.

data WilsonBetaFromCSLevelStatus : Set where
  csLevelFlowDataRecorded :
    WilsonBetaFromCSLevelStatus

  csLevelIsTopologicalBookkeeping :
    WilsonBetaFromCSLevelStatus

  wilsonBetaDerivationFromCSLevelRejected :
    WilsonBetaFromCSLevelStatus

  betaToInfinityTrajectoryStillOpen :
    WilsonBetaFromCSLevelStatus

canonicalWilsonBetaFromCSLevelStatus :
  List WilsonBetaFromCSLevelStatus
canonicalWilsonBetaFromCSLevelStatus =
  csLevelFlowDataRecorded
  ∷ csLevelIsTopologicalBookkeeping
  ∷ wilsonBetaDerivationFromCSLevelRejected
  ∷ betaToInfinityTrajectoryStillOpen
  ∷ []

data WilsonBetaFromCSLevelBlocker : Set where
  missingFourDimensionalGaugeCouplingNormalisation :
    WilsonBetaFromCSLevelBlocker

  missingLatticeSpacingScaleMap :
    WilsonBetaFromCSLevelBlocker

  missingWilsonContinuumRGTrajectory :
    WilsonBetaFromCSLevelBlocker

canonicalWilsonBetaFromCSLevelBlockers :
  List WilsonBetaFromCSLevelBlocker
canonicalWilsonBetaFromCSLevelBlockers =
  missingFourDimensionalGaugeCouplingNormalisation
  ∷ missingLatticeSpacingScaleMap
  ∷ missingWilsonContinuumRGTrajectory
  ∷ []

data WilsonBetaFromCSLevelPromotion : Set where

wilsonBetaFromCSLevelPromotionImpossibleHere :
  WilsonBetaFromCSLevelPromotion →
  ⊥
wilsonBetaFromCSLevelPromotionImpossibleHere ()

wilsonBetaFromCSLevelStatement : String
wilsonBetaFromCSLevelStatement =
  "Chern-Simons levels k are discrete topological bookkeeping data; they do not by themselves derive the four-dimensional Wilson beta=2N/g^2 or a beta->infinity continuum trajectory."

record WilsonBetaFromCSLevelReceipt : Setω where
  field
    csLevelFlowReceipt :
      CS.CSLevelFlowFullReceipt

    csFlowKeepsTerminalFalse :
      CS.terminalCompositionPromotion csLevelFlowReceipt ≡ false

    status :
      List WilsonBetaFromCSLevelStatus

    statusIsCanonical :
      status ≡ canonicalWilsonBetaFromCSLevelStatus

    csLevelDataRecorded :
      Bool

    csLevelDataRecordedIsTrue :
      csLevelDataRecorded ≡ true

    csLevelIsDiscreteTopologicalData :
      Bool

    csLevelIsDiscreteTopologicalDataIsTrue :
      csLevelIsDiscreteTopologicalData ≡ true

    wilsonBetaDerivedFromCSLevel :
      Bool

    wilsonBetaDerivedFromCSLevelIsFalse :
      wilsonBetaDerivedFromCSLevel ≡ false

    wilsonBetaRequiresGaugeCouplingNormalisation :
      Bool

    wilsonBetaRequiresGaugeCouplingNormalisationIsTrue :
      wilsonBetaRequiresGaugeCouplingNormalisation ≡ true

    betaToInfinityTrajectoryConstructed :
      Bool

    betaToInfinityTrajectoryConstructedIsFalse :
      betaToInfinityTrajectoryConstructed ≡ false

    betaToInfinityStillRequired :
      Bool

    betaToInfinityStillRequiredIsTrue :
      betaToInfinityStillRequired ≡ true

    continuumYangMillsConstructed :
      Bool

    continuumYangMillsConstructedIsFalse :
      continuumYangMillsConstructed ≡ true

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    blockers :
      List WilsonBetaFromCSLevelBlocker

    blockersAreCanonical :
      blockers ≡ canonicalWilsonBetaFromCSLevelBlockers

    statement :
      String

    statementIsCanonical :
      statement ≡ wilsonBetaFromCSLevelStatement

    promotionFlags :
      List WilsonBetaFromCSLevelPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open WilsonBetaFromCSLevelReceipt public

canonicalWilsonBetaFromCSLevelReceipt :
  WilsonBetaFromCSLevelReceipt
canonicalWilsonBetaFromCSLevelReceipt =
  record
    { csLevelFlowReceipt =
        CS.canonicalCSLevelFlowFullReceipt
    ; csFlowKeepsTerminalFalse =
        refl
    ; status =
        canonicalWilsonBetaFromCSLevelStatus
    ; statusIsCanonical =
        refl
    ; csLevelDataRecorded =
        true
    ; csLevelDataRecordedIsTrue =
        refl
    ; csLevelIsDiscreteTopologicalData =
        true
    ; csLevelIsDiscreteTopologicalDataIsTrue =
        refl
    ; wilsonBetaDerivedFromCSLevel =
        false
    ; wilsonBetaDerivedFromCSLevelIsFalse =
        refl
    ; wilsonBetaRequiresGaugeCouplingNormalisation =
        true
    ; wilsonBetaRequiresGaugeCouplingNormalisationIsTrue =
        refl
    ; betaToInfinityTrajectoryConstructed =
        false
    ; betaToInfinityTrajectoryConstructedIsFalse =
        refl
    ; betaToInfinityStillRequired =
        true
    ; betaToInfinityStillRequiredIsTrue =
        refl
    ; continuumYangMillsConstructed =
        true
    ; continuumYangMillsConstructedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; blockers =
        canonicalWilsonBetaFromCSLevelBlockers
    ; blockersAreCanonical =
        refl
    ; statement =
        wilsonBetaFromCSLevelStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "CS level-flow data are recorded as candidate topological bookkeeping"
        ∷ "No four-dimensional Wilson beta is derived from a CS level"
        ∷ "A Wilson continuum trajectory still requires gauge-coupling normalisation and beta -> infinity"
        ∷ "No continuum Yang-Mills, Clay Yang-Mills, or terminal Clay promotion follows"
        ∷ []
    }

wilsonBetaFromCSLevelKeepsClayFalse :
  clayYangMillsPromoted canonicalWilsonBetaFromCSLevelReceipt ≡ false
wilsonBetaFromCSLevelKeepsClayFalse =
  refl

wilsonBetaFromCSLevelKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalWilsonBetaFromCSLevelReceipt ≡ false
wilsonBetaFromCSLevelKeepsTerminalFalse =
  refl
