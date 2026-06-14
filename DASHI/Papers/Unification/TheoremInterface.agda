module DASHI.Papers.Unification.TheoremInterface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.UnificationConsumerAuthorityAssemblyBoundary
  as Authority
import DASHI.Physics.Closure.UnificationCrossTermNullityTheoremBoundary
  as UCT
import DASHI.Physics.Closure.UnificationFourPointStressCompositeBoundary
  as FourPoint
import DASHI.Physics.Closure.UnificationJordanVonNeumannAdapterBoundary
  as JvN
import DASHI.Physics.Closure.UnificationPromotionProbeCutsetReceipt
  as Probe
import DASHI.Physics.Closure.UnificationScaleInvariantCrossTermHypothesisBoundary
  as U1aH
import DASHI.Promotion.UnificationCriticalPathReceipt
  as Critical

------------------------------------------------------------------------
-- Paper-facing Unification theorem/status interface.
--
-- This module is a bounded wrapper over existing UCT receipts.  It exposes
-- the paper grammar for UCT.1-UCT.8 and terminal unification while preserving
-- all open theorem and terminal-promotion flags as false.

paperInterfaceStatement : String
paperInterfaceStatement =
  "Paper-facing Unification interface: UCT.1-UCT.8 theorem grammar and consumer surfaces are imported from existing fail-closed receipts; UCT.1-UCT.4 remain the live wall; terminal unification promotion remains false."

data UnificationPaperStatus : Set where
  importedUCTReceiptsAssembled_terminalFalse :
    UnificationPaperStatus

record UnificationPaperTheoremInterface : Setω where
  field
    status :
      UnificationPaperStatus

    statusIsCanonical :
      status ≡ importedUCTReceiptsAssembled_terminalFalse

    correctedCrossTermHypothesisBoundary :
      U1aH.UnificationScaleInvariantCrossTermHypothesisBoundary

    crossTermNullityTheoremBoundary :
      UCT.UnificationCrossTermNullityTheoremBoundary

    fourPointStressCompositeBoundary :
      FourPoint.UnificationFourPointStressCompositeBoundary

    jordanVonNeumannAdapterBoundary :
      JvN.UnificationJordanVonNeumannAdapterBoundary

    consumerAuthorityAssemblyBoundary :
      Authority.UnificationConsumerAuthorityAssemblyBoundary

    promotionProbeCutsetReceipt :
      Probe.UnificationPromotionProbeCutsetReceipt

    criticalPathReceipt :
      Critical.UnificationCriticalPathReceipt

    uct1ResidualPDEHypothesesStillOpen :
      UCT.residualPDEHypothesesSpecified
        crossTermNullityTheoremBoundary
      ≡ false

    uct2EllipticParabolicClassStillOpen :
      UCT.ellipticityOrParabolicityClassSpecified
        crossTermNullityTheoremBoundary
      ≡ false

    uct3CarlemanIntakeStillOpen :
      UCT.carlemanHypothesesSpecified
        crossTermNullityTheoremBoundary
      ≡ false

    uct4CrossTermNullityTargetRecorded :
      UCT.actualTheoremTargetRecorded crossTermNullityTheoremBoundary
      ≡ true

    uct4CrossTermNullityStillOpen :
      UCT.crossTermNullityTheoremProved crossTermNullityTheoremBoundary
      ≡ false

    uct5ModuloNullConsumerRecorded :
      UCT.moduloNullLinearityConsumerRecorded
        crossTermNullityTheoremBoundary
      ≡ true

    uct5ModuloNullLinearityStillOpen :
      UCT.moduloNullLinearityProved crossTermNullityTheoremBoundary
      ≡ false

    uct6FourPointConsumerRecorded :
      UCT.fourPointConsumerRecorded crossTermNullityTheoremBoundary
      ≡ true

    uct6FourPointConsumerStillOpen :
      UCT.fourPointConsumerProved crossTermNullityTheoremBoundary
      ≡ false

    uct7ParallelogramConsumerRecorded :
      UCT.parallelogramConsumerRecorded crossTermNullityTheoremBoundary
      ≡ true

    uct7ParallelogramStillOpen :
      UCT.parallelogramProved crossTermNullityTheoremBoundary
      ≡ false

    uct8JordanVonNeumannConsumerRecorded :
      UCT.jordanVonNeumannAdapterConsumerRecorded
        crossTermNullityTheoremBoundary
      ≡ true

    uct8JordanVonNeumannStillOpen :
      UCT.jordanVonNeumannAdapterProved crossTermNullityTheoremBoundary
      ≡ false

    uct8AdapterPromotionStillFalse :
      JvN.promotionFlag jordanVonNeumannAdapterBoundary ≡ false

    downstreamAuthorityTerminalStillFalse :
      Authority.TerminalUnificationPromotionEnabled ≡ false

    fourPointStressTerminalStillFalse :
      FourPoint.terminalUnificationPromoted
        fourPointStressCompositeBoundary
      ≡ false

    crossTermTerminalStillFalse :
      UCT.terminalPromotion crossTermNullityTheoremBoundary ≡ false

    probeUnificationPromotionStillFalse :
      Probe.unificationPromotionClaimed promotionProbeCutsetReceipt
      ≡ false

    criticalPathTerminalStillFalse :
      Critical.terminalPromotion criticalPathReceipt ≡ false

    terminalUnificationPromoted :
      Bool

    terminalUnificationPromotedMatchesCriticalPath :
      terminalUnificationPromoted
      ≡ Critical.terminalPromotion criticalPathReceipt

    terminalUnificationPromotedIsFalse :
      terminalUnificationPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ paperInterfaceStatement

    exactSummary :
      List String

open UnificationPaperTheoremInterface public

canonicalUnificationPaperTheoremInterface :
  UnificationPaperTheoremInterface
canonicalUnificationPaperTheoremInterface =
  record
    { status =
        importedUCTReceiptsAssembled_terminalFalse
    ; statusIsCanonical =
        refl
    ; correctedCrossTermHypothesisBoundary =
        U1aH.canonicalUnificationScaleInvariantCrossTermHypothesisBoundary
    ; crossTermNullityTheoremBoundary =
        UCT.canonicalUnificationCrossTermNullityTheoremBoundary
    ; fourPointStressCompositeBoundary =
        FourPoint.canonicalUnificationFourPointStressCompositeBoundary
    ; jordanVonNeumannAdapterBoundary =
        JvN.canonicalUnificationJordanVonNeumannAdapterBoundary
    ; consumerAuthorityAssemblyBoundary =
        Authority.canonicalUnificationConsumerAuthorityAssemblyBoundary
    ; promotionProbeCutsetReceipt =
        Probe.canonicalUnificationPromotionProbeCutsetReceipt
    ; criticalPathReceipt =
        Critical.canonicalUnificationCriticalPathReceipt
    ; uct1ResidualPDEHypothesesStillOpen =
        refl
    ; uct2EllipticParabolicClassStillOpen =
        refl
    ; uct3CarlemanIntakeStillOpen =
        refl
    ; uct4CrossTermNullityTargetRecorded =
        refl
    ; uct4CrossTermNullityStillOpen =
        UCT.crossTermNullityTheoremProvedIsFalse
          UCT.canonicalUnificationCrossTermNullityTheoremBoundary
    ; uct5ModuloNullConsumerRecorded =
        refl
    ; uct5ModuloNullLinearityStillOpen =
        UCT.moduloNullLinearityProvedIsFalse
          UCT.canonicalUnificationCrossTermNullityTheoremBoundary
    ; uct6FourPointConsumerRecorded =
        refl
    ; uct6FourPointConsumerStillOpen =
        UCT.fourPointConsumerProvedIsFalse
          UCT.canonicalUnificationCrossTermNullityTheoremBoundary
    ; uct7ParallelogramConsumerRecorded =
        refl
    ; uct7ParallelogramStillOpen =
        UCT.parallelogramProvedIsFalse
          UCT.canonicalUnificationCrossTermNullityTheoremBoundary
    ; uct8JordanVonNeumannConsumerRecorded =
        refl
    ; uct8JordanVonNeumannStillOpen =
        UCT.jordanVonNeumannAdapterProvedIsFalse
          UCT.canonicalUnificationCrossTermNullityTheoremBoundary
    ; uct8AdapterPromotionStillFalse =
        JvN.canonicalJordanVonNeumannPromotionFalse
    ; downstreamAuthorityTerminalStillFalse =
        Authority.UnificationConsumerAuthorityAssemblyBoundary.terminalPromotionStillFalse
          Authority.canonicalUnificationConsumerAuthorityAssemblyBoundary
    ; fourPointStressTerminalStillFalse =
        FourPoint.canonicalFourPointStressTerminalPromotionFalse
    ; crossTermTerminalStillFalse =
        UCT.terminalPromotionIsFalse
          UCT.canonicalUnificationCrossTermNullityTheoremBoundary
    ; probeUnificationPromotionStillFalse =
        Probe.unificationPromotionProbeCutsetKeepsPromotionFalse
    ; criticalPathTerminalStillFalse =
        Critical.canonicalUnificationCriticalPathTerminalPromotionFalse
    ; terminalUnificationPromoted =
        Critical.terminalPromotion Critical.canonicalUnificationCriticalPathReceipt
    ; terminalUnificationPromotedMatchesCriticalPath =
        refl
    ; terminalUnificationPromotedIsFalse =
        Critical.canonicalUnificationCriticalPathTerminalPromotionFalse
    ; statement =
        paperInterfaceStatement
    ; statementIsCanonical =
        refl
    ; exactSummary =
        "UCT.1 residual PDE hypotheses remain unspecified."
        ∷ "UCT.2 elliptic/parabolic class and UCT.3 Carleman intake remain unspecified."
        ∷ "UCT.4 cross-term nullity is a recorded theorem target, not a proved theorem."
        ∷ "UCT.5-UCT.8 consumer surfaces are recorded and fail-closed."
        ∷ "Critical path, authority assembly, probe cutset, four-point stress, and JvN adapter receipts all keep terminal unification false."
        ∷ []
    }

unificationPaperInterfaceTerminalFalse :
  terminalUnificationPromoted canonicalUnificationPaperTheoremInterface
  ≡ false
unificationPaperInterfaceTerminalFalse =
  Critical.canonicalUnificationCriticalPathTerminalPromotionFalse

unificationPaperInterfaceUCT4StillOpen :
  UCT.crossTermNullityTheoremProved
    (crossTermNullityTheoremBoundary
      canonicalUnificationPaperTheoremInterface)
  ≡ false
unificationPaperInterfaceUCT4StillOpen =
  UCT.crossTermNullityTheoremProvedIsFalse
    UCT.canonicalUnificationCrossTermNullityTheoremBoundary
