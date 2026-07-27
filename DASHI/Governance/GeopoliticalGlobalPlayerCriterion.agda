module DASHI.Governance.GeopoliticalGlobalPlayerCriterion where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Set₁)
open import Data.Nat.Base using (_≤_)

open import DASHI.Governance.GeopoliticalDifferentialEvidence

------------------------------------------------------------------------
-- Explicit threshold semantics for the phrase "global player".
--
-- The generic evidence schema deliberately permits different methodological
-- criteria.  This executable refinement requires the selected currency and
-- three numerical lower bounds to be visible in the receipt.

record ConcreteGlobalPlayerCriterion : Set where
  constructor concreteGlobalPlayerCriterion
  field
    requiredCurrency : CurrencyUnit
    minimumExportWholeUnits : Nat
    minimumGlobalShareBasisPoints : Nat
    minimumCompanyCount : Nat
    criterionReferenceYear : Nat
    criterionMethodology : String

open ConcreteGlobalPlayerCriterion public

record ConcreteGlobalPlayerSupported
  (criterion : ConcreteGlobalPlayerCriterion)
  (evidence : CyberExportEvidence)
  : Set₁ where
  constructor concreteGlobalPlayerSupported
  field
    exportCurrencyMatches :
      unit (exportValue evidence) ≡ requiredCurrency criterion

    exportThresholdMet :
      minimumExportWholeUnits criterion
      ≤ wholeUnits (exportValue evidence)

    globalShareThresholdMet :
      minimumGlobalShareBasisPoints criterion
      ≤ globalShareBasisPoints evidence

    companyThresholdMet :
      minimumCompanyCount criterion
      ≤ companyCount evidence

    referenceYearMatches :
      referenceYear evidence ≡ criterionReferenceYear criterion

open ConcreteGlobalPlayerSupported public

record GlobalPlayerComparisonReceipt
  (criterion : ConcreteGlobalPlayerCriterion)
  (evidence : CyberExportEvidence)
  : Set₁ where
  constructor globalPlayerComparisonReceipt
  field
    support : ConcreteGlobalPlayerSupported criterion evidence
    methodologyCompatibilityReceipt : String
    denominatorCompatibilityReceipt : String

-- In particular, an aggregate high-tech export total cannot inhabit a
-- cyber-specific criterion unless its methodology and denominator receipts
-- explicitly justify that projection.
