module DASHI.Physics.Closure.E6HyperformH3H2CommonActionBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.E6HyperformH3H2NineSheetChartExact as Nine
import DASHI.Physics.Closure.E6HyperformH3H2InvariantQuadraticDynamicsExact as Quadratic
import DASHI.Physics.Foundations.HistoryLocalActionAccumulationExact as Local
import DASHI.Physics.Foundations.CommonEffectiveActionVariationExact as Common
import DASHI.Physics.Foundations.EinsteinCommonActionVariationFrontierExact as Einstein
import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld

------------------------------------------------------------------------
-- H3-H2 FINITE ACTION -> CANONICAL COMMON-ACTION GR/QFT FRONTIER
--
-- The nine H2 decorations over one H3 already form the affine F3^2 fibre with
-- invariant displacement d^2.  Here that exact carrier is inserted into the
-- repository's existing LocalActionSystem rather than introducing a parallel
-- action formalism.
--
-- A one-step action is the balanced finite quadratic displacement
--
--   d^2(u,v) in {0,1,2}.
--
-- The master HistoryLocalActionAccumulation owner then supplies exact additive
-- finite-history accumulation.  This still does NOT define a continuum metric
-- variation or stress tensor; those remain explicit fields of the canonical
-- CommonEffectiveActionVariation / EinsteinTensorVariationReceipt interfaces.
------------------------------------------------------------------------

subCoeff : Nine.F3Coeff → Nine.F3Coeff → Nine.F3Coeff
subCoeff Nine.c0 Nine.c0 = Nine.c0
subCoeff Nine.c0 Nine.c1 = Nine.c2
subCoeff Nine.c0 Nine.c2 = Nine.c1
subCoeff Nine.c1 Nine.c0 = Nine.c1
subCoeff Nine.c1 Nine.c1 = Nine.c0
subCoeff Nine.c1 Nine.c2 = Nine.c2
subCoeff Nine.c2 Nine.c0 = Nine.c2
subCoeff Nine.c2 Nine.c1 = Nine.c1
subCoeff Nine.c2 Nine.c2 = Nine.c0

squareCode : Nine.F3Coeff → Nat
squareCode Nine.c0 = 0
squareCode Nine.c1 = 1
squareCode Nine.c2 = 1

fibreDisplacementAction :
  Nine.PhaseAffineCoordinate → Nine.PhaseAffineCoordinate → Nat
fibreDisplacementAction (b , c) (b' , c') =
  squareCode (subCoeff b b') + squareCode (subCoeff c c')

h3h2LocalActionSystem : Local.LocalActionSystem
h3h2LocalActionSystem = record
  { Local.LocalActionSystem.State = Nine.PhaseAffineCoordinate
  ; Local.LocalActionSystem.localAction = fibreDisplacementAction
  ; Local.LocalActionSystem.actionReading =
      "H3-H2 fibre step cost = d^2(u,v), the affine-O(2,3)-invariant quadratic displacement"
  }

h3h2HistoryAction : List (Local.Step h3h2LocalActionSystem) → Nat
h3h2HistoryAction = Local.historyAction h3h2LocalActionSystem

h3h2HistoryActionAppend :
  (left right : List (Local.Step h3h2LocalActionSystem)) →
  h3h2HistoryAction (left ++ right)
  ≡ h3h2HistoryAction left + h3h2HistoryAction right
h3h2HistoryActionAppend = Local.historyActionAppend h3h2LocalActionSystem

------------------------------------------------------------------------
-- Physical promotion contract.
--
-- The finite action is fixed above.  A physical promotion must supply a
-- CommonEffectiveActionVariation whose literal finite-action carrier is this
-- same object, then independently pay the GR metric-variation theorem and the
-- QFT total-stress identification.  Once those are paid, the canonical master
-- compiler closes the same-stress weld; no T=G/kappa definition is inserted.
------------------------------------------------------------------------

record H3H2CommonActionPhysicalPromotion
    (U : Weld.UnifiedCandidate) : Set₁ where
  field
    variation : Common.CommonEffectiveActionVariation U
    sameFiniteLocalActionSystem :
      Common.localActionSystem variation ≡ h3h2LocalActionSystem
    einsteinMetricVariation :
      Einstein.EinsteinTensorVariationReceipt variation
    qftTotalStressIdentification :
      Common.QFTVariationIdentification variation
    stressWeldToken : Weld.StressEnergyWeldToken U
open H3H2CommonActionPhysicalPromotion public

compileH3H2CommonActionStressWeld :
  ∀ {U : Weld.UnifiedCandidate} →
  H3H2CommonActionPhysicalPromotion U →
  Weld.SameStressEnergyWeld U
compileH3H2CommonActionStressWeld promotion =
  Common.commonVariationImpliesStressWeld
    (variation promotion)
    (Einstein.einsteinTensorVariationBuildsGRIdentification
      (variation promotion)
      (einsteinMetricVariation promotion))
    (qftTotalStressIdentification promotion)
    (stressWeldToken promotion)

record H3H2CommonActionBridgeBoundary : Set where
  constructor h3-h2-common-action-bridge-boundary
  field
    finiteNineStateLocalActionSystemPaid : Bool
    displacementUsesSameAffineF3SquaredCarrier : Bool
    masterHistoryActionAdditivityReused : Bool
    symmetryDerivedKineticShapeAlreadyPaid : Bool
    physicalEffectiveSourceVariationPaid : Bool
    einsteinCommonMetricVariationPaid : Bool
    qftTotalStressIdentificationPaid : Bool
    physicalStressWeldPaid : Bool
    finiteActionDefinesStressByFiat : Bool
    boundary : String
open H3H2CommonActionBridgeBoundary public

canonicalBoundary : H3H2CommonActionBridgeBoundary
canonicalBoundary =
  h3-h2-common-action-bridge-boundary
    true true true true
    false false false false false
    "The H3-H2 order-parameter fibre now inhabits the repository's canonical finite LocalActionSystem with step cost equal to its intrinsic quadratic displacement, and master history additivity is reused directly. Physical promotion is deliberately routed through CommonEffectiveActionVariation, EinsteinTensorVariationReceipt and QFTVariationIdentification; no stress tensor is defined from the finite action or from G by fiat."

quadraticReceipt : Quadratic.H3H2InvariantQuadraticDynamicsLocalReceipt
quadraticReceipt = Quadratic.canonicalH3H2InvariantQuadraticDynamicsLocalReceipt
