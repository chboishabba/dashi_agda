module DASHI.ComputerScience.GodelConcreteCodecProofDebtExact where

open import DASHI.Core.Prelude

import DASHI.Core.ProofDebtRouterExact as Debt

------------------------------------------------------------------------
-- CONCRETE GÖDEL CODEC / REPRESENTABILITY PROOF-DEBT SPLIT
------------------------------------------------------------------------

-- The source-written base-12 Nat retraction is a repo-derived statement whose
-- mathematical content is already explicit in source.  Until an exact-head
-- kernel receipt exists, it remains certification debt rather than a theorem
-- success claim.
base12NatRetractionCertificationRoute : Debt.ProofDebtRoutingReceipt
base12NatRetractionCertificationRoute =
  Debt.proof-debt-routing-receipt
    Debt.deductiveTheorem
    Debt.derivedInRepo
    Debt.sourceAligned
    Debt.uncertified
    Debt.localAgda
    Debt.certificationDebt
    refl

-- The general primitive-recursive representability theorem is established
-- mathematics, but our local contract has not yet been exact-source aligned.
primitiveRecursiveRepresentabilityAlignmentRoute :
  Debt.ProofDebtRoutingReceipt
primitiveRecursiveRepresentabilityAlignmentRoute =
  Debt.proof-debt-routing-receipt
    Debt.deductiveTheorem
    Debt.sourceEstablished
    Debt.transcribedUnaligned
    Debt.proofDeferred
    Debt.sourceOnly
    Debt.transcriptionDebt
    refl

-- The exact statement that the custom base-12 self-substitution function is
-- primitive recursive is repo-specific.  We keep it on the mathematical side
-- until a same-code theorem reduces it to source-established closure results.
base12SelfSubstitutionPrimitiveRecursiveRoute :
  Debt.ProofDebtRoutingReceipt
base12SelfSubstitutionPrimitiveRecursiveRoute =
  Debt.proof-debt-routing-receipt
    Debt.deductiveTheorem
    Debt.novelOpen
    Debt.sourceAligned
    Debt.proofDeferred
    Debt.localAgda
    Debt.mathematicalDebt
    refl

base12RetractionIsCertificationDebt :
  Debt.routedDebt base12NatRetractionCertificationRoute
  ≡ Debt.certificationDebt
base12RetractionIsCertificationDebt = refl

representabilityNeedsAlignment :
  Debt.routedDebt primitiveRecursiveRepresentabilityAlignmentRoute
  ≡ Debt.transcriptionDebt
representabilityNeedsAlignment = refl

base12SelfSubstitutionStillMathematicalDebt :
  Debt.routedDebt base12SelfSubstitutionPrimitiveRecursiveRoute
  ≡ Debt.mathematicalDebt
base12SelfSubstitutionStillMathematicalDebt = refl

------------------------------------------------------------------------
-- Firewall: the three debts are not interchangeable.
------------------------------------------------------------------------

data CodecKernelReceiptPaysRepresentabilityAlignment : Set where
data HistoricalRepresentabilityPaysCustomBase12PR : Set where
data SourceAlignmentEqualsKernelCertification : Set where

codecCertificationDoesNotAlignRepresentability :
  CodecKernelReceiptPaysRepresentabilityAlignment → ⊥
codecCertificationDoesNotAlignRepresentability ()

historicalTheoremDoesNotPayCustomCodePR :
  HistoricalRepresentabilityPaysCustomBase12PR → ⊥
historicalTheoremDoesNotPayCustomBase12PR ()

alignmentDoesNotEqualCertification :
  SourceAlignmentEqualsKernelCertification → ⊥
alignmentDoesNotEqualCertification ()

record GodelConcreteCodecProofDebtBoundary : Set where
  constructor godelConcreteCodecProofDebtBoundary
  field
    base12RetractionRoutedToCertification : Bool
    representabilityRoutedToAlignment : Bool
    customSelfSubstitutionRoutedToMathematics : Bool
    debtClassesCollapsed : Bool

canonicalGodelConcreteCodecProofDebtBoundary :
  GodelConcreteCodecProofDebtBoundary
canonicalGodelConcreteCodecProofDebtBoundary =
  godelConcreteCodecProofDebtBoundary true true true false
