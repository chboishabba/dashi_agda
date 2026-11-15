module DASHI.Physics.Chemistry.Nobel2026SoaiMechanisticKineticWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Physics.Chemistry.Nobel2026ChiralitySourceAtlasExact as Atlas

------------------------------------------------------------------------
-- SOURCE-PAID SOAI MECHANISTIC / KINETIC WELD
--
-- Möhler et al. 2025 expose enough of the fitted reaction-network architecture
-- in the main article to replace the previous generic "kinetics needed" seam
-- with a same-reaction typed surface.  Equation bodies from the supplementary
-- material are not guessed.  Counts, units, selected constants, activation
-- barriers, mirror-cycle equality and mechanistic roles below are source-paid.
------------------------------------------------------------------------

data SoaiSystem : Set where
  TMSPyr : SoaiSystem
  AdPyr : SoaiSystem
  TMSPym : SoaiSystem
  AdPym : SoaiSystem

data RateCoordinate : Set where
  k2 k3 k4 k5 k6 k7 k8 kMinus2 kMinus3 kMinus4 : RateCoordinate

data RateUnit : Set where
  perMolarSecond : RateUnit
  perSecond : RateUnit

rateUnit : RateCoordinate → RateUnit
rateUnit k2 = perMolarSecond
rateUnit k3 = perMolarSecond
rateUnit k4 = perMolarSecond
rateUnit k5 = perMolarSecond
rateUnit k6 = perSecond
rateUnit k7 = perMolarSecond
rateUnit k8 = perSecond
rateUnit kMinus2 = perSecond
rateUnit kMinus3 = perSecond
rateUnit kMinus4 = perSecond

k4Unit : rateUnit k4 ≡ perMolarSecond
k4Unit = refl

k6Unit : rateUnit k6 ≡ perSecond
k6Unit = refl

record KineticNetworkScale : Set where
  constructor kineticNetworkScale
  field
    autocatalyticODECount : Nat
    sideReactionODECount : Nat
    totalODECount : Nat
    profilesPerIterationApprox : Nat

mohler2025NetworkScale : KineticNetworkScale
mohler2025NetworkScale = kineticNetworkScale 18 1 19 24000000

networkCountCloses :
  KineticNetworkScale.autocatalyticODECount mohler2025NetworkScale
  + KineticNetworkScale.sideReactionODECount mohler2025NetworkScale
  ≡ KineticNetworkScale.totalODECount mohler2025NetworkScale
networkCountCloses = refl

------------------------------------------------------------------------
-- Activation barriers are stored in deci-kJ/mol to retain the published one
-- decimal place exactly as Nat data.
------------------------------------------------------------------------

activationBarrierDeciKJPerMol : SoaiSystem → Nat
activationBarrierDeciKJPerMol TMSPyr = 946
activationBarrierDeciKJPerMol AdPyr = 955
activationBarrierDeciKJPerMol TMSPym = 859
activationBarrierDeciKJPerMol AdPym = 864

tmsPyrBarrier : activationBarrierDeciKJPerMol TMSPyr ≡ 946
tmsPyrBarrier = refl

adPyrBarrier : activationBarrierDeciKJPerMol AdPyr ≡ 955
adPyrBarrier = refl

tmsPymBarrier : activationBarrierDeciKJPerMol TMSPym ≡ 859
tmsPymBarrier = refl

adPymBarrier : activationBarrierDeciKJPerMol AdPym ≡ 864
adPymBarrier = refl

------------------------------------------------------------------------
-- Source-exposed mechanistic roles.
------------------------------------------------------------------------

data KineticRole : Set where
  alkoxideFormation : KineticRole
  homoHeterochiralDimerEquilibrium : KineticRole
  hemiacetalFormationRateDetermining : KineticRole
  fastReactantCoordination : KineticRole
  slowerAlkylTransfer : KineticRole
  secondFastAldehydeCoordination : KineticRole
  slowCycleClosingDissociation : KineticRole

data AggregationSurface : Set where
  homoHeterochiralDimers : AggregationSurface
  historicalTetramericTransitionState : AggregationSurface
  transientHemiacetalateCatalyst : AggregationSurface

record MechanisticReceipt : Set where
  constructor mechanisticReceipt
  field
    source : Source.AttributedSource
    mirrorCyclesUseSameRates : Bool
    mirrorCyclesUseSameRatesIsTrue : mirrorCyclesUseSameRates ≡ true
    aldehydeOrderTwoAcrossInvestigatedSystems : Bool
    aldehydeOrderTwoAcrossInvestigatedSystemsIsTrue :
      aldehydeOrderTwoAcrossInvestigatedSystems ≡ true
    k4IsRateDetermining : Bool
    k4IsRateDeterminingIsTrue : k4IsRateDetermining ≡ true
    dimersEnterSelfAmplificationExplanation : Bool
    dimersEnterSelfAmplificationExplanationIsTrue :
      dimersEnterSelfAmplificationExplanation ≡ true
    hemiacetalatePathwaySupported : Bool
    hemiacetalatePathwaySupportedIsTrue : hemiacetalatePathwaySupported ≡ true

mohler2025MechanisticReceipt : MechanisticReceipt
mohler2025MechanisticReceipt =
  mechanisticReceipt
    Atlas.mohler2025
    true refl
    true refl
    true refl
    true refl
    true refl

-- Fast formation of isopropylzinc alkoxide (R)-1: 1.5e2 M^-1 s^-1.
alkoxideFormationRatePerMolarSecond : Nat
alkoxideFormationRatePerMolarSecond = 150

alkoxideFormationRateValue : alkoxideFormationRatePerMolarSecond ≡ 150
alkoxideFormationRateValue = refl

record SoaiMechanisticKineticBoundary : Set where
  constructor soaiMechanisticKineticBoundary
  field
    sameReactionODEArchitecturePaid : Bool
    selectedRateUnitsPaid : Bool
    selectedRateConstantPaid : Bool
    activationBarrierTablePaid : Bool
    mirrorCycleRateIdentityPaid : Bool
    rateDeterminingStepPaid : Bool
    aldehydeSecondOrderPaid : Bool
    aggregationAndCatalystRolesSeparated : Bool
    supplementaryEquationBodiesInvented : Bool
    historicalTetramerCollapsedIntoHemiacetalCatalyst : Bool

canonicalSoaiMechanisticKineticBoundary : SoaiMechanisticKineticBoundary
canonicalSoaiMechanisticKineticBoundary =
  soaiMechanisticKineticBoundary
    true true true true true true true true false false
