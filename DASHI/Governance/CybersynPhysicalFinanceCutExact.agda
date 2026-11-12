module DASHI.Governance.CybersynPhysicalFinanceCutExact where

-- DASHI-original, source-preserving finite stress-test kernel (2026-11-12).
-- Uses upstream Cybernetic viability gates and intergenerational planning.
-- Real world values, customary authority and causal effects are NOT inferred.
-- Source rule: Docs/SourceAttributionPolicy.md.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Governance.CybersynGlobalViabilityMaxCutExact as Cyber
import DASHI.Core.IntergenerationalPlanningHorizonExact as Future
import DASHI.Economics.AIGlobalFundingRegulatorySynthesisExact as Finance
import DASHI.Economics.GeopoliticalEnergyAITreasuryTransmissionExact as Geo

infixr 6 _and_
_and_ : Bool → Bool → Bool
true and b = b
false and _ = false

-- Financial flow uses two-sided posting. A new loan creates equal borrower
-- purchasing power and liability; it is not earned terminal-customer cash.
record DoubleEntryPosting : Set where
  constructor posting
  field
    newCashAsset : Nat
    newDebtLiability : Nat
    doubleEntry : newCashAsset ≡ newDebtLiability

open DoubleEntryPosting public

loanPosting : Nat → DoubleEntryPosting
loanPosting amount = posting amount amount refl

loanPostingBalanced : (amount : Nat) →
  newCashAsset (loanPosting amount) ≡
  newDebtLiability (loanPosting amount)
loanPostingBalanced amount = doubleEntry (loanPosting amount)

-- Explicit cost flows: an allocated amount can be consumed or retained.
-- Using the same symbolic quantity on both sides makes accounting identity
-- constructive, rather than assuming balance from a Bool flag.
record Allocation (Source Use : Set) : Set₁ where
  constructor allocation
  field
    supplied : Source
    applied : Source → Use
    receipt : Use
    allocationCorrect : receipt ≡ applied supplied

open Allocation public

record CashAllocation : Set where
  constructor cashAllocation
  field
    capitalAvailable : Nat
    projectSpending : Nat
    cashReserve : Nat
    sourcesEqualUses :
      capitalAvailable ≡ projectSpending + cashReserve

open CashAllocation public

allocateCash : (spending reserve : Nat) → CashAllocation
allocateCash spending reserve =
  cashAllocation (spending + reserve) spending reserve refl

cashAllocationBalances : (spending reserve : Nat) →
  capitalAvailable (allocateCash spending reserve) ≡
  projectSpending (allocateCash spending reserve) +
  cashReserve (allocateCash spending reserve)
cashAllocationBalances spending reserve = refl

-- Disaggregated physical constraints cannot be replaced by dollars.
record PhysicalAllocation : Set where
  constructor physicalAllocation
  field
    totalGridCapacity : Nat
    gridToAI : Nat
    gridToHouseholds : Nat
    gridToOtherProduction : Nat
    unusedGrid : Nat
    gridBalance :
      totalGridCapacity ≡
      gridToAI + (gridToHouseholds + (gridToOtherProduction + unusedGrid))
    totalSkilledHours : Nat
    skilledHoursHousing : Nat
    skilledHoursDataCentre : Nat
    skilledHoursOther : Nat
    labourBalance :
      totalSkilledHours ≡
      skilledHoursHousing + (skilledHoursDataCentre + skilledHoursOther)

open PhysicalAllocation public

allocatePhysical :
  (ai home industry idle housing dataCentre other : Nat) →
  PhysicalAllocation
allocatePhysical ai home industry idle housing dataCentre other =
  physicalAllocation
    (ai + (home + (industry + idle)))
    ai home industry idle refl
    (housing + (dataCentre + other))
    housing dataCentre other refl

-- Same physical budget, different distribution. Both cases are internally
-- consistent; the example does not claim actual Australian quantities.
housingPriority : PhysicalAllocation
housingPriority = allocatePhysical 2 3 1 0 6 1 1

dataCentrePriority : PhysicalAllocation
dataCentrePriority = allocatePhysical 2 3 1 0 1 6 1

sameAggregateGrid :
  totalGridCapacity housingPriority ≡
  totalGridCapacity dataCentrePriority
sameAggregateGrid = refl

sameAggregateTrades :
  totalSkilledHours housingPriority ≡
  totalSkilledHours dataCentrePriority
sameAggregateTrades = refl

differentHousingAllocations :
  skilledHoursHousing housingPriority ≡
  skilledHoursHousing dataCentrePriority → ⊥
differentHousingAllocations ()

-- Gross investment or gross labour demand alone is not the housing outcome.
data AggregateAnnouncement : Set where
  sameCapitalAndJobs : AggregateAnnouncement

data AllocationCase : Set where
  housingCase : AllocationCase
  dataCentreCase : AllocationCase

announced : AllocationCase → AggregateAnnouncement
announced _ = sameCapitalAndJobs

housingUse : AllocationCase → Nat
housingUse housingCase = skilledHoursHousing housingPriority
housingUse dataCentreCase = skilledHoursHousing dataCentrePriority

announcementCannotFixHousingUse :
  (f : AggregateAnnouncement → Nat) →
  ((c : AllocationCase) → housingUse c ≡ f (announced c)) → ⊥
announcementCannotFixHousingUse f proof with proof housingCase | proof dataCentreCase
... | refl | ()

-- Requiring all seven generations is stronger than endpoint inspection.
sevenSafe : (Future.Generation → Bool) → Bool
sevenSafe f =
  f Future.generation1 and
  f Future.generation2 and
  f Future.generation3 and
  f Future.generation4 and
  f Future.generation5 and
  f Future.generation6 and
  f Future.generation7

earlyHarm : Future.Generation → Bool
earlyHarm Future.generation1 = false
earlyHarm Future.generation2 = true
earlyHarm Future.generation3 = true
earlyHarm Future.generation4 = true
earlyHarm Future.generation5 = true
earlyHarm Future.generation6 = true
earlyHarm Future.generation7 = true

lateSuccessNotAllGenerationsSafe :
  earlyHarm Future.generation7 ≡ true
lateSuccessNotAllGenerationsSafe = refl

earlyHarmBlocksWholeHorizon : sevenSafe earlyHarm ≡ false
earlyHarmBlocksWholeHorizon = refl

allGenerationsSafe : Future.Generation → Bool
allGenerationsSafe _ = true

completeHorizonAccepted : sevenSafe allGenerationsSafe ≡ true
completeHorizonAccepted = refl

-- Governance cannot be replaced by a favourable economic balance sheet.
-- Fold verified balances only into the corresponding financial/infrastructure
-- coordinates; other coordinates still demand separate admitted evidence.
partialViabilityFromBalances : Bool → Bool → Bool → Bool →
  Bool → Bool → Cyber.ViabilityGates
partialViabilityFromBalances provisioning ecology futureSafe
  communityAuthority correction sourceAdmitted =
  Cyber.viabilityGates
    provisioning ecology futureSafe true true
    communityAuthority correction sourceAdmitted

balancesWithoutAuthorityStillFail :
  Cyber.viable
    (partialViabilityFromBalances true true true false true true) ≡ false
balancesWithoutAuthorityStillFail = refl

-- Exact cross-owner references do not pretend to admit the candidate edges.
fundingSynthesisOwner : Finance.UbiquityFundingContradiction
fundingSynthesisOwner = Finance.canonicalUbiquityFundingContradiction

geopoliticalOwner : Geo.CandidateEdge
geopoliticalOwner = Geo.yenToTreasuryFunding
