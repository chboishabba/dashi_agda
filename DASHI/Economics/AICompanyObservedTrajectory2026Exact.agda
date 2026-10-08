module DASHI.Economics.AICompanyObservedTrajectory2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Economics.AICompanyReturnRolloverTrajectory2026Exact as Company

------------------------------------------------------------------------
-- ENTITY-SCOPED X_t TRAJECTORIES
--
-- These are comparable same-company/same-horizon observations.  They discharge
-- the need for a second comparable observation at the entity trajectory level,
-- but they do not promote to the global AI-capital state without a separate
-- aggregation / terminal-payer authority bridge.
------------------------------------------------------------------------

record CompanyObservedStatePoint : Set where
  constructor companyObservedStatePoint
  field
    company : String
    period : String
    horizonProtocol : String
    realisedPeriod : Company.RealisedOperatingPeriod
    concentration : Company.ConcentrationIntervalTrajectory
    capitalRecoveryCertified : Bool
    globalStatePromotionAllowed : Bool

open CompanyObservedStatePoint public

coreWeaveX2025 : CompanyObservedStatePoint
coreWeaveX2025 = companyObservedStatePoint
  "CoreWeave" "H1-2025" "H1"
  Company.coreWeaveH12025
  Company.coreWeaveConcentrationTrajectory
  false false

coreWeaveX2026 : CompanyObservedStatePoint
coreWeaveX2026 = companyObservedStatePoint
  "CoreWeave" "H1-2026" "H1"
  Company.coreWeaveH12026
  Company.coreWeaveConcentrationTrajectory
  false false

cerebrasX2025 : CompanyObservedStatePoint
cerebrasX2025 = companyObservedStatePoint
  "Cerebras" "H1-2025" "H1"
  Company.cerebrasH12025
  Company.cerebrasConcentrationTrajectory
  false false

cerebrasX2026 : CompanyObservedStatePoint
cerebrasX2026 = companyObservedStatePoint
  "Cerebras" "H1-2026" "H1"
  Company.cerebrasH12026
  Company.cerebrasConcentrationTrajectory
  false false

record CompanyObservedTransition : Set where
  constructor companyObservedTransition
  field
    from : CompanyObservedStatePoint
    to : CompanyObservedStatePoint
    sameCompany : Bool
    sameHorizonProtocol : Bool
    realisedRevenueGrew : Bool
    realisedConcentrationLowerFell : Bool
    globalStatePromotionAllowed : Bool
    capitalRecoveryTransitionCertified : Bool

open CompanyObservedTransition public

coreWeaveH1Trajectory : CompanyObservedTransition
coreWeaveH1Trajectory = companyObservedTransition
  coreWeaveX2025 coreWeaveX2026 true true true true false false

cerebrasH1Trajectory : CompanyObservedTransition
cerebrasH1Trajectory = companyObservedTransition
  cerebrasX2025 cerebrasX2026 true true true true false false

------------------------------------------------------------------------
-- Forward concentration and rollover remain separate coordinates.
------------------------------------------------------------------------

record CompanyTrajectoryAugmentation : Set where
  constructor companyTrajectoryAugmentation
  field
    company : String
    realisedTrajectoryPresent : Bool
    payerConcentrationTrajectoryPresent : Bool
    rolloverOrAmortisationPresent : Bool
    forwardRevenueConcentrationPresent : Bool
    realisedROICPresent : Bool
    waccPresent : Bool
    terminalPayerVectorComplete : Bool

coreWeaveTrajectoryAugmentation : CompanyTrajectoryAugmentation
coreWeaveTrajectoryAugmentation = companyTrajectoryAugmentation
  "CoreWeave" true true true false false false false

cerebrasTrajectoryAugmentation : CompanyTrajectoryAugmentation
cerebrasTrajectoryAugmentation = companyTrajectoryAugmentation
  "Cerebras" true true true true false false false

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data EntityTrajectoryImpliesGlobalStatePermission : Set where
data RevenueGrowthImpliesCapitalRecoveryTransitionPermission : Set where
data ConcentrationDeclineImpliesIndependentTerminalPayerPermission : Set where

entityTrajectoryDoesNotAutoPromoteGlobalState :
  EntityTrajectoryImpliesGlobalStatePermission → ⊥
entityTrajectoryDoesNotAutoPromoteGlobalState ()

revenueGrowthDoesNotAutoCertifyCapitalRecoveryTransition :
  RevenueGrowthImpliesCapitalRecoveryTransitionPermission → ⊥
revenueGrowthDoesNotAutoCertifyCapitalRecoveryTransition ()

concentrationDeclineDoesNotAutoCertifyIndependentTerminalPayer :
  ConcentrationDeclineImpliesIndependentTerminalPayerPermission → ⊥
concentrationDeclineDoesNotAutoCertifyIndependentTerminalPayer ()

coreWeaveTrajectoryStillNotGlobal :
  globalStatePromotionAllowed coreWeaveH1Trajectory ≡ false
coreWeaveTrajectoryStillNotGlobal = refl

cerebrasTrajectoryStillNotCapitalRecovery :
  capitalRecoveryTransitionCertified cerebrasH1Trajectory ≡ false
cerebrasTrajectoryStillNotCapitalRecovery = refl
