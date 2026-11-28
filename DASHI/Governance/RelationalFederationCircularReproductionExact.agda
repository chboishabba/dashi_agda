module DASHI.Governance.RelationalFederationCircularReproductionExact where

-- DASHI-native accounting and observer composition. External sources:
-- UNEP FI, Financing Circularity (2020); Ellen MacArthur Foundation,
-- Financing the circular economy (2020); DCCEEW circular economy framework.
-- See Docs/RelationalFederationCircularReproduction20261129.md.
-- No actual transaction, corruption, ecological outcome or authority inferred.
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Education.DigitalESDPoliticalEconomyProvisioningExact as ESD
import DASHI.Governance.CybersynPhysicalFinanceCutExact as Finance
import DASHI.Cognition.HeritageProject2025TrumpImplementationExact as P2025
import DASHI.Governance.RelationalFederationScopedViabilityExact as Scope

wasteSourceAtlas : Attr.AttributedSourceAtlas
wasteSourceAtlas = ESD.canonicalPoliticalEconomySourceAtlas

implementationArchitectureSource : P2025.Project2025Receipt
implementationArchitectureSource = P2025.fourPillarsReceipt

-- The actual existing double-entry constructor, not a new loan ontology.
newLoan : Nat → Finance.DoubleEntryPosting
newLoan = Finance.loanPosting

-- The same clearing amount is both internal debit and internal credit.
-- This identity pays neither liquidity at each node nor legal settlement.
record InternalClearing (amount : Nat) : Set where
  constructor clearing
  field
    debit credit : Nat
    debitMatches : debit ≡ amount
    creditMatches : credit ≡ amount

internalClearing : (amount : Nat) → InternalClearing amount
internalClearing n = clearing n n refl refl

-- These are nonnegative realised flows in a declared currency and period.
-- Debt drawdown, grant, service income and principal repayment are separate.
record FinancePeriod
  (opening externalService grants debtDraw internalIn internalOut
   operating maintenance care interest principal closing : Nat) : Set where
  field
    cashBalance :
      opening + (externalService + (grants + (debtDraw + internalIn)))
      ≡ internalOut + (operating + (maintenance + (care +
        (interest + (principal + closing)))))

record LiabilityPeriod (opening draw principal closing : Nat) : Set where
  field
    principalBalance : opening + draw ≡ principal + closing

-- Physical units and use scopes are externally specified. Reuse the scoped
-- stock owner instead of treating a monetary flow as a material quantity.
materialBalance : (use loss retained : Nat) →
  Scope.StockBalance 0 (use + (loss + retained)) use loss retained
materialBalance = Scope.stockConstructive

-- Counterexample: identical gross payments can be funded by independent
-- service receipts or by a debt draw. A cycle is not an income certificate.
data FundingFixture : Set where
  serviceFunded debtFunded : FundingFixture

grossPayment : FundingFixture → Nat
grossPayment _ = 10

externalServiceIncome : FundingFixture → Nat
externalServiceIncome serviceFunded = 10
externalServiceIncome debtFunded = 0

grossCannotDetermineServiceIncome :
  NF.FactorsThrough grossPayment externalServiceIncome → ⊥
grossCannotDetermineServiceIncome =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness serviceFunded debtFunded refl (λ ()))

-- Equal material recovery does not imply equal absolute virgin throughput.
data MaterialFixture : Set where
  reducedThroughput reboundThroughput : MaterialFixture

recoveredMaterial : MaterialFixture → Nat
recoveredMaterial _ = 8

virginInput : MaterialFixture → Nat
virginInput reducedThroughput = 2
virginInput reboundThroughput = 12

recoveryCannotDetermineVirginInput :
  NF.FactorsThrough recoveredMaterial virginInput → ⊥
recoveryCannotDetermineVirginInput =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness reducedThroughput reboundThroughput refl (λ ()))

-- Same-scope independent gates, not a score or proof of empirical adequacy.
record ReproductionAdmission (Target : Set)
  (Cash Ledger Material Ecology Care Access Authority : Target → Set)
  (t : Target) : Set where
  field
    cashWitness : Cash t
    liabilityWitness : Ledger t
    physicalWitness : Material t
    ecologyWitness : Ecology t
    careWitness : Care t
    accessWitness : Access t
    authorityWitness : Authority t
