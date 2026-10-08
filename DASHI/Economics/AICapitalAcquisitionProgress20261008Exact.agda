module DASHI.Economics.AICapitalAcquisitionProgress20261008Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Economics.AICapitalObservedStateTimeSeries2026Exact as Global
import DASHI.Economics.AICompanyObservedTrajectory2026Exact as Entity
import DASHI.Economics.AICompanyReturnRolloverTrajectory2026Exact as Company

------------------------------------------------------------------------
-- SCOPED ACQUISITION PROGRESS, 2026-10-08
------------------------------------------------------------------------

data EvidenceScope : Set where
  entityScope : EvidenceScope
  selectedComponentScope : EvidenceScope
  globalComplexScope : EvidenceScope

data ClosureState : Set where
  open : ClosureState
  partial : ClosureState
  closed : ClosureState

record ProducerProgress : Set where
  constructor producerProgress
  field
    producer : String
    scope : EvidenceScope
    closure : ClosureState
    receipt : String
    promotesGlobalClosure : Bool

open ProducerProgress public

coreWeaveRolloverProgress : ProducerProgress
coreWeaveRolloverProgress = producerProgress
  "rollover / maturity schedule"
  entityScope closed
  "CoreWeave June 30 2026 debt maturity table provides a complete stated principal schedule for the entity"
  false

cerebrasLoanAmortisationProgress : ProducerProgress
cerebrasLoanAmortisationProgress = producerProgress
  "customer-financed loan amortisation"
  entityScope partial
  "OpenAI working-capital loan has stated 6% rate, current/long-term split, service-credit repayments, delivery-triggered amortisation and 2032 legal maturity; cash timing remains conditional"
  false

coreWeaveReturnProgress : ProducerProgress
coreWeaveReturnProgress = producerProgress
  "realised return trajectory"
  entityScope partial
  "H1-2025/H1-2026 revenue, operating income, interest, CFO, capex and D&A are comparable; realised ROIC and WACC remain absent"
  false

cerebrasReturnProgress : ProducerProgress
cerebrasReturnProgress = producerProgress
  "realised return trajectory"
  entityScope partial
  "H1-2025/H1-2026 revenue, operating result, CFO, capex and D&A are comparable; realised ROIC and WACC remain absent"
  false

coreWeavePayerProgress : ProducerProgress
coreWeavePayerProgress = producerProgress
  "payer concentration trajectory"
  entityScope partial
  "largest-customer share falls from 73 percent of 2025 revenue to 52 percent of H1-2026 revenue; independent-terminal-payer status is not thereby established"
  false

cerebrasPayerProgress : ProducerProgress
cerebrasPayerProgress = producerProgress
  "payer concentration trajectory"
  entityScope partial
  "realised H1 concentration interval narrows while forward RPO has a significant OpenAI component; terminal-payer provenance remains open"
  false

entityPersistenceProgress : ProducerProgress
entityPersistenceProgress = producerProgress
  "persistence trajectory"
  entityScope closed
  "CoreWeave and Cerebras each now have comparable H1-2025 -> H1-2026 state pairs under fixed entity/horizon comparison keys"
  false

globalPersistenceProgress : ProducerProgress
globalPersistenceProgress = producerProgress
  "persistence trajectory"
  globalComplexScope open
  "the global AI-capital X_t series still lacks a second point with comparable graph/fundamental coverage"
  false

globalRolloverProgress : ProducerProgress
globalRolloverProgress = producerProgress
  "rollover dependence"
  globalComplexScope open
  "entity maturity schedules do not yet produce a weighted complex-wide rollover coordinate"
  false

globalCapitalSpreadProgress : ProducerProgress
globalCapitalSpreadProgress = producerProgress
  "realised ROIC-WACC"
  globalComplexScope open
  "filings provide operating and cash-flow trajectories but no admissible same-entity realised ROIC-WACC join yet"
  false

------------------------------------------------------------------------
-- Scope firewalls.
------------------------------------------------------------------------

data EntityClosureImpliesGlobalClosurePermission : Set where
data EntityPersistenceImpliesGlobalPersistencePermission : Set where
data DebtScheduleImpliesCapitalSpreadPermission : Set where

entityClosureDoesNotAutoPromoteGlobalClosure :
  EntityClosureImpliesGlobalClosurePermission → ⊥
entityClosureDoesNotAutoPromoteGlobalClosure ()

entityPersistenceDoesNotAutoPromoteGlobalPersistence :
  EntityPersistenceImpliesGlobalPersistencePermission → ⊥
entityPersistenceDoesNotAutoPromoteGlobalPersistence ()

debtScheduleDoesNotAutoCreateCapitalSpread :
  DebtScheduleImpliesCapitalSpreadPermission → ⊥
debtScheduleDoesNotAutoCreateCapitalSpread ()

coreWeaveEntityRolloverIsClosed : closure coreWeaveRolloverProgress ≡ closed
coreWeaveEntityRolloverIsClosed = refl

globalRolloverStillOpen : closure globalRolloverProgress ≡ open
globalRolloverStillOpen = refl

entityPersistenceIsClosed : closure entityPersistenceProgress ≡ closed
entityPersistenceIsClosed = refl

globalPersistenceStillOpen : closure globalPersistenceProgress ≡ open
globalPersistenceStillOpen = refl

currentGlobalPointStillNonPromotable :
  Global.promotionReady Global.currentObservedCapitalState20261007 ≡ false
currentGlobalPointStillNonPromotable = refl

coreWeaveEntityTrajectoryStillNotGlobal :
  Entity.globalStatePromotionAllowed Entity.coreWeaveH1Trajectory ≡ false
coreWeaveEntityTrajectoryStillNotGlobal = refl

coreWeaveROICStillUnknown : Company.realisedROICKnown Company.coreWeaveH12026 ≡ false
coreWeaveROICStillUnknown = refl
