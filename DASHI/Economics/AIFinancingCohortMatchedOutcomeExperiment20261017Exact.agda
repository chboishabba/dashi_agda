module DASHI.Economics.AIFinancingCohortMatchedOutcomeExperiment20261017Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Economics.AIContractBackedFinancingReplication20261016Exact as Replication

record CohortSubject : Set where
  constructor cohort-subject
  field
    subjectName : String
    economicLayer : String
    contractLinkedFinancingObserved : Bool
    customerPrepaymentObserved : Bool
    gpuCollateralObserved : Bool
    projectFinanceObserved : Bool

open CohortSubject public

coreWeaveSubject : CohortSubject
coreWeaveSubject = cohort-subject
  "CoreWeave" "neocloud / compute provider" true false true true

nebiusSubject : CohortSubject
nebiusSubject = cohort-subject
  "Nebius" "neocloud / compute provider" true false true true

irenSubject : CohortSubject
irenSubject = cohort-subject
  "IREN" "neocloud / data-centre operator" true true true true

sharonAISubject : CohortSubject
sharonAISubject = cohort-subject
  "Sharon AI" "neocloud / compute provider" true false true true

aibNebiusSubject : CohortSubject
aibNebiusSubject = cohort-subject
  "AIB/Nebius 50 MW" "data-centre developer / landlord" true true false true

record MatchedComparatorRequirements : Set where
  constructor matched-comparator-requirements
  field
    layerDeclared : Bool
    customerCreditBasisDeclared : Bool
    financingInstrumentDeclared : Bool
    collateralBasisDeclared : Bool
    prepaymentTreatmentDeclared : Bool
    maturityHorizonDeclared : Bool
    spreadOrCouponBasisDeclared : Bool
    capexDenominatorDeclared : Bool
    realisedReturnBasisDeclared : Bool
    refinancingOutcomeDefinitionDeclared : Bool
    distressOutcomeDefinitionDeclared : Bool

open MatchedComparatorRequirements public

canonicalComparatorRequirements : MatchedComparatorRequirements
canonicalComparatorRequirements = matched-comparator-requirements
  true true true true true true true true true true true

record FinancingCohortExperiment : Set where
  constructor financing-cohort-experiment
  field
    subjectCount : Nat
    matchedComparatorDeclared : Bool
    crossCompanyMechanismReplicationPaid : Bool
    crossLayerMechanismReplicationPaid : Bool
    sameAccountingBasisPaid : Bool
    sameMaturityHorizonPaid : Bool
    sameCustomerCreditBasisPaid : Bool
    realisedProjectReturnPaid : Bool
    realisedRefinancingOutcomePaid : Bool
    realisedDefaultOrRestructuringPaid : Bool
    allRealisedOutcomeCoordinatesPaid : Bool
    mechanismSimilaritySelectsOutcome : Bool
    oneStressedIssuerSelectsCohort : Bool

open FinancingCohortExperiment public

currentCohortExperiment : FinancingCohortExperiment
currentCohortExperiment = financing-cohort-experiment
  5 true true true false false false false false false false false false

matchedComparatorContractPaid : matchedComparatorDeclared currentCohortExperiment ≡ true
matchedComparatorContractPaid = refl

crossCompanyMechanismPaid : crossCompanyMechanismReplicationPaid currentCohortExperiment ≡ true
crossCompanyMechanismPaid = refl

crossLayerMechanismPaid : crossLayerMechanismReplicationPaid currentCohortExperiment ≡ true
crossLayerMechanismPaid = refl

mechanismSimilarityDoesNotSelectOutcome : mechanismSimilaritySelectsOutcome currentCohortExperiment ≡ false
mechanismSimilarityDoesNotSelectOutcome = refl

oneIssuerStressDoesNotSelectCohort : oneStressedIssuerSelectsCohort currentCohortExperiment ≡ false
oneIssuerStressDoesNotSelectCohort = refl

realisedOutcomesRemainOpen : allRealisedOutcomeCoordinatesPaid currentCohortExperiment ≡ false
realisedOutcomesRemainOpen = refl

data FinancingMechanismImpliesReturnPermission : Set where
data CrossCompanyMechanismImpliesSectorStressPermission : Set where
data ValidatorSimilarityImpliesConsumerOutcomePermission : Set where

financingMechanismDoesNotCreateReturn : FinancingMechanismImpliesReturnPermission → ⊥
financingMechanismDoesNotCreateReturn ()

crossCompanyMechanismDoesNotCreateSectorStress : CrossCompanyMechanismImpliesSectorStressPermission → ⊥
crossCompanyMechanismDoesNotCreateSectorStress ()

validatorSimilarityDoesNotCreateConsumerOutcome : ValidatorSimilarityImpliesConsumerOutcomePermission → ⊥
validatorSimilarityDoesNotCreateConsumerOutcome ()

boundary : String
boundary =
  "This is the economics-domain matched-cohort continuation inspired by the repository's claim-relative/same-object evaluation discipline, without importing unmerged sibling theorem authority. The validator-side object is financing-mechanism comparability; the consumer-side object is realised economic outcome. CoreWeave, Nebius, IREN, Sharon AI and the AIB/Nebius developer project now provide a five-subject mechanism cohort spanning compute-provider and developer layers. The comparator contract requires layer, customer-credit, financing-instrument, collateral, prepayment, maturity, spread/coupon, capex denominator, realised-return and distress/refinancing definitions to be declared before promotion. Current public evidence pays mechanism replication but not matched accounting/horizon/customer-credit bases or realised project-return/refinancing/default coordinates. Mechanism similarity therefore cannot select a common outcome, and CoreWeave stress cannot select the cohort regime by itself."
