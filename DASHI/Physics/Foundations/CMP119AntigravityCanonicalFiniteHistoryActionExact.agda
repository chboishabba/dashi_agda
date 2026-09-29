{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCanonicalFiniteHistoryActionExact where

------------------------------------------------------------------------
-- CMP109 inverse-square trajectory + CMP119 Wilson-node action on ONE
-- finite mode/history object.  g_k is taken directly from the already
-- established positive active-scale history, while c_k is DEFINED as u_k.
-- In particular we do NOT make the false identification g_k := u_k.
--
-- The remaining physical-source obligation is to show that the selected
-- CMP119 Wilson/E/R/B/vacuum family really has this normalized assembly.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_)
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as Finite
import DASHI.Physics.YangMills.Balaban1989FiniteModeInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4RationalInverseSquareOrderExact as Order
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalSourceSectorActionExact as Sector
import DASHI.Physics.Foundations.CMP119AntigravityRawActionIncrementResidualExact as Edge

module _
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom : Set}
    {betaData : Finite.FiniteModeBetaTrajectoryData trajectory Mode Atom}
    (history :
      History.FiniteModeInverseSquareTerminalHistoryData
        trajectory Mode Atom betaData)
    {Density Background Fluctuation : Set}
    (sectors : Sector.CMP119NormalizedSectorSource
      Density Background Fluctuation)
  where

  physicalHistorySectors :
    Sector.CMP119NormalizedSectorSource
      Density Background Fluctuation
  physicalHistorySectors = record
    { Sector.CMP119NormalizedSectorSource.terminalScale =
        Sector.terminalScale sectors
    ; Sector.CMP119NormalizedSectorSource.couplingAt =
        History.couplingAt history
    ; Sector.CMP119NormalizedSectorSource.densityAt =
        Sector.densityAt sectors
    ; Sector.CMP119NormalizedSectorSource.backgroundAt =
        Sector.backgroundAt sectors
    ; Sector.CMP119NormalizedSectorSource.fluctuationAt =
        Sector.fluctuationAt sectors
    ; Sector.CMP119NormalizedSectorSource.eAt =
        Sector.eAt sectors
    ; Sector.CMP119NormalizedSectorSource.rAt =
        Sector.rAt sectors
    ; Sector.CMP119NormalizedSectorSource.bAt =
        Sector.bAt sectors
    ; Sector.CMP119NormalizedSectorSource.vacuumAt =
        Sector.vacuumAt sectors
    }

  physicalHistoryAction :
    Raw.CMP119SourceNativeRawState
      Density Background Fluctuation
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
  physicalHistoryAction =
    Sector.canonicalRawState trajectory physicalHistorySectors

  samePhysicalCoupling : ∀ k →
    Raw.runningCoupling physicalHistoryAction k
    ≡ History.couplingAt history k
  samePhysicalCoupling k = refl

  sameWilsonInverseCoupling : ∀ k →
    Raw.wilsonCoefficient physicalHistoryAction k
    ≡ Flow.inverseCoupling trajectory k
  sameWilsonInverseCoupling =
    Sector.wilsonCoefficientIsCMP109Inverse trajectory
      physicalHistorySectors

  actualInverseSquareNormalization : ∀ k →
    Raw.wilsonCoefficient physicalHistoryAction k
      * Order.square (Raw.runningCoupling physicalHistoryAction k)
    ≡ 1ℚ
  actualInverseSquareNormalization =
    History.inverseCouplingRepresentation history

  sameSourceCorrectedBeta : ∀ k →
    Flow.beta trajectory (suc k)
    ≡ Edge.projectedSourceEdge physicalHistoryAction k
      - (Sector.sectorProjection trajectory physicalHistorySectors k
       - Sector.sectorProjection trajectory physicalHistorySectors (suc k))
  sameSourceCorrectedBeta =
    Sector.sourceBetaIsProjectedEdgeMinusFourSectorDrift
      trajectory physicalHistorySectors
