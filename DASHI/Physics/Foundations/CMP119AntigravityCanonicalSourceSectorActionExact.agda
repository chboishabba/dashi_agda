{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCanonicalSourceSectorActionExact where

------------------------------------------------------------------------
-- NORMALIZED CMP119 NODE ACTION / EXPLICIT E,R,B,V PROJECTOR DRIFT
--
-- This is a concrete (not axiomatically same-object) rational action
-- constructor.  It takes the four source-native NON-WILSON sectors and
-- the finite CMP109 coupling history; the Wilson coefficient and complete
-- Eq.(2.23) action are then DEFINED from those inputs.
--
-- Source relevance remains conditional: the supplied sector functions must
-- still be shown equal to the selected CMP119 E/R/B/vacuum sector objects.
-- Do not mistake this representation construction for that physical proof.
--
-- CMP109: Bałaban, Commun. Math. Phys. 109 (1987), 249--301.
-- CMP119: Bałaban, Commun. Math. Phys. 119 (1988), 243--285.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _+_; _-_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.Foundations.CMP119AntigravityRawActionIncrementResidualExact as Edge

canonicalAssemble :
  ℚ → T4.LocalizedAction → T4.LocalizedAction →
  T4.LocalizedAction → T4.LocalizedAction → T4.LocalizedAction →
  T4.LocalizedAction
canonicalAssemble c w e r b v =
  T4.addLocalizedAction (T4.scaleLocalizedAction c w)
    (T4.addLocalizedAction e
      (T4.addLocalizedAction r (T4.addLocalizedAction b v)))

canonicalAlgebra :
  Raw.CMP119RawActionAlgebra
    T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
    T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
canonicalAlgebra = record
  { Raw.CMP119RawActionAlgebra.assemble = canonicalAssemble }

record CMP119NormalizedSectorSource
    (Density Background Fluctuation : Set) : Set₁ where
  field
    terminalScale : Nat
    -- This is g_k, NOT inverse coupling u_k. Source-specific inverse-
    -- square representation is a separate physical proof.
    couplingAt : Nat → ℚ
    densityAt : Nat → Density
    backgroundAt : Nat → Background
    fluctuationAt : Nat → Fluctuation
    eAt rAt bAt vacuumAt : Nat → T4.LocalizedAction

open CMP119NormalizedSectorSource public

module _
    {Density Background Fluctuation : Set}
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (sectors : CMP119NormalizedSectorSource
      Density Background Fluctuation)
  where

  canonicalNodeAction : Nat → T4.LocalizedAction
  canonicalNodeAction k =
    canonicalAssemble
      (Flow.inverseCoupling trajectory k)
      T4.plaquetteBasisAction
      (eAt sectors k) (rAt sectors k)
      (bAt sectors k) (vacuumAt sectors k)

  canonicalRawState :
    Raw.CMP119SourceNativeRawState
      Density Background Fluctuation
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
  canonicalRawState = record
    { Raw.CMP119SourceNativeRawState.terminalScale =
        terminalScale sectors
    ; Raw.CMP119SourceNativeRawState.effectiveDensity =
        densityAt sectors
    ; Raw.CMP119SourceNativeRawState.backgroundField =
        backgroundAt sectors
    ; Raw.CMP119SourceNativeRawState.fluctuationFields =
        fluctuationAt sectors
    ; Raw.CMP119SourceNativeRawState.runningCoupling =
        couplingAt sectors
    ; Raw.CMP119SourceNativeRawState.wilsonActionTerm =
        λ _ → T4.plaquetteBasisAction
    ; Raw.CMP119SourceNativeRawState.regularSmallFieldTerm =
        eAt sectors
    ; Raw.CMP119SourceNativeRawState.rOperationTerm =
        rAt sectors
    ; Raw.CMP119SourceNativeRawState.boundaryTerm =
        bAt sectors
    ; Raw.CMP119SourceNativeRawState.vacuumEnergy =
        vacuumAt sectors
    ; Raw.CMP119SourceNativeRawState.effectiveAction =
        canonicalNodeAction
    ; Raw.CMP119SourceNativeRawState.actionAlgebra =
        canonicalAlgebra
    ; Raw.CMP119SourceNativeRawState.wilsonCoefficient =
        Flow.inverseCoupling trajectory
    ; Raw.CMP119SourceNativeRawState.equation223 =
        λ _ → refl
    }

  wilsonCoefficientIsCMP109Inverse :
    ∀ k →
    Raw.wilsonCoefficient canonicalRawState k
    ≡ Flow.inverseCoupling trajectory k
  wilsonCoefficientIsCMP109Inverse k = refl

  sectorProjection : Nat → ℚ
  sectorProjection k =
    T4.plaquetteCoefficientProjector (eAt sectors k)
    + (T4.plaquetteCoefficientProjector (rAt sectors k)
    + (T4.plaquetteCoefficientProjector (bAt sectors k)
    + T4.plaquetteCoefficientProjector (vacuumAt sectors k)))

  nonWilsonProjectorIsSectorSum :
    ∀ k →
    Edge.nodeResidual canonicalRawState k
    ≡ sectorProjection k
  nonWilsonProjectorIsSectorSum k =
    ℚRing.solve-∀
      (Flow.inverseCoupling trajectory k)
      (T4.plaquetteCoefficientProjector (eAt sectors k))
      (T4.plaquetteCoefficientProjector (rAt sectors k))
      (T4.plaquetteCoefficientProjector (bAt sectors k))
      (T4.plaquetteCoefficientProjector (vacuumAt sectors k))

  nonWilsonDriftIsFourSectorDifference :
    ∀ k →
    Edge.nodeResidual canonicalRawState k
      - Edge.nodeResidual canonicalRawState (suc k)
    ≡ sectorProjection k - sectorProjection (suc k)
  nonWilsonDriftIsFourSectorDifference k
    rewrite nonWilsonProjectorIsSectorSum k
          | nonWilsonProjectorIsSectorSum (suc k) = refl

  sourceBetaIsProjectedEdgeMinusFourSectorDrift :
    ∀ k →
    Flow.beta trajectory (suc k)
    ≡ Edge.projectedSourceEdge canonicalRawState k
      - (sectorProjection k - sectorProjection (suc k))
  sourceBetaIsProjectedEdgeMinusFourSectorDrift k =
    trans
      (Edge.selectedSourceBetaIsCorrectedProjectedEdge
        canonicalRawState trajectory
        wilsonCoefficientIsCMP109Inverse k)
      (cong
        (λ drift →
          Edge.projectedSourceEdge canonicalRawState k - drift)
        (nonWilsonDriftIsFourSectorDifference k))
