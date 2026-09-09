module DASHI.ComputerScience.GodelNamedLimitsProofDebtBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Core.ProofDebtRouterExact as Debt
import DASHI.ComputerScience.GodelTuringNamedLimitsSourceStatusAtlasExact as Atlas

------------------------------------------------------------------------
-- NAMED LIMITS -> CANONICAL PROOF-DEBT ROUTER
--
-- The theorem family is source-established, but the new abstract contracts are
-- deliberately not claimed to be exact source-aligned transcriptions yet.
-- Therefore the current theorem-level debt is transcription/alignment debt,
-- not certification debt.  Gödel numbering itself is an implemented substrate
-- and remains a separate local-certification coordinate.
------------------------------------------------------------------------

sourceTheoremNeedsAlignment : Debt.ProofDebtRoutingReceipt
sourceTheoremNeedsAlignment =
  Debt.proof-debt-routing-receipt
    Debt.deductiveTheorem
    Debt.sourceEstablished
    Debt.transcribedUnaligned
    Debt.proofDeferred
    Debt.sourceOnly
    Debt.transcriptionDebt
    refl

sourceMetadataAndAlignmentPending : Debt.ProofDebtRoutingReceipt
sourceMetadataAndAlignmentPending =
  Debt.proof-debt-routing-receipt
    Debt.deductiveTheorem
    Debt.sourceEstablished
    Debt.notTranscribed
    Debt.proofDeferred
    Debt.sourceOnly
    Debt.transcriptionDebt
    refl

namedLimitRoute : Atlas.NamedLimitProblem → Debt.ProofDebtRoutingReceipt
namedLimitRoute Atlas.godelNumbering =
  Debt.proof-debt-routing-receipt
    Debt.deductiveTheorem
    Debt.derivedInRepo
    Debt.sourceAligned
    Debt.uncertified
    Debt.localAgda
    Debt.certificationDebt
    refl
namedLimitRoute Atlas.arithmetisedSubstitution = sourceTheoremNeedsAlignment
namedLimitRoute Atlas.representabilityOfProofRelation = sourceTheoremNeedsAlignment
namedLimitRoute Atlas.diagonalFixedPointLemma = sourceTheoremNeedsAlignment
namedLimitRoute Atlas.godelFirstIncompleteness = sourceTheoremNeedsAlignment
namedLimitRoute Atlas.hilbertBernaysDerivabilityConditions = sourceTheoremNeedsAlignment
namedLimitRoute Atlas.godelSecondIncompleteness = sourceTheoremNeedsAlignment
namedLimitRoute Atlas.lobTheorem = sourceTheoremNeedsAlignment
namedLimitRoute Atlas.tarskiUndefinability = sourceMetadataAndAlignmentPending
namedLimitRoute Atlas.churchEntscheidungsproblem = sourceTheoremNeedsAlignment
namedLimitRoute Atlas.turingHaltingUndecidability = sourceTheoremNeedsAlignment
namedLimitRoute Atlas.kleeneRecursionFixedPoint = sourceTheoremNeedsAlignment
namedLimitRoute Atlas.riceTheorem = sourceTheoremNeedsAlignment
namedLimitRoute Atlas.busyBeaverNoncomputability = sourceTheoremNeedsAlignment

------------------------------------------------------------------------
-- Exact current regressions.
------------------------------------------------------------------------

godelNumberingIsCertificationDebtOnly :
  Debt.routedDebt (namedLimitRoute Atlas.godelNumbering)
  ≡ Debt.certificationDebt
godelNumberingIsCertificationDebtOnly = refl

godelINeedsAlignmentBeforeCertification :
  Debt.routedDebt (namedLimitRoute Atlas.godelFirstIncompleteness)
  ≡ Debt.transcriptionDebt
godelINeedsAlignmentBeforeCertification = refl

godelIINeedsAlignmentBeforeCertification :
  Debt.routedDebt (namedLimitRoute Atlas.godelSecondIncompleteness)
  ≡ Debt.transcriptionDebt
godelIINeedsAlignmentBeforeCertification = refl

lobNeedsAlignmentBeforeCertification :
  Debt.routedDebt (namedLimitRoute Atlas.lobTheorem)
  ≡ Debt.transcriptionDebt
lobNeedsAlignmentBeforeCertification = refl

turingNeedsAlignmentBeforeCertification :
  Debt.routedDebt (namedLimitRoute Atlas.turingHaltingUndecidability)
  ≡ Debt.transcriptionDebt
turingNeedsAlignmentBeforeCertification = refl

riceNeedsAlignmentBeforeCertification :
  Debt.routedDebt (namedLimitRoute Atlas.riceTheorem)
  ≡ Debt.transcriptionDebt
riceNeedsAlignmentBeforeCertification = refl

busyBeaverNeedsAlignmentBeforeCertification :
  Debt.routedDebt (namedLimitRoute Atlas.busyBeaverNoncomputability)
  ≡ Debt.transcriptionDebt
busyBeaverNeedsAlignmentBeforeCertification = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SourceEstablishedMeansSourceAligned : Set where
data AbstractContractMeansTheoremCertified : Set where
data ExistingGodelNumberMeansIncompletenessClosed : Set where

sourceEstablishedDoesNotMeanAligned : SourceEstablishedMeansSourceAligned → ⊥
sourceEstablishedDoesNotMeanAligned ()

abstractContractDoesNotCertifyTheorem : AbstractContractMeansTheoremCertified → ⊥
abstractContractDoesNotCertifyTheorem ()

godelNumberingDoesNotCloseIncompleteness :
  ExistingGodelNumberMeansIncompletenessClosed → ⊥
godelNumberingDoesNotCloseIncompleteness ()

record GodelNamedLimitsProofDebtBoundary : Set where
  constructor godelNamedLimitsProofDebtBoundary
  field
    implementedNumberingRoutedSeparately : Bool
    theoremSourcesNeedExactAlignment : Bool
    alignmentDebtIsCertificationDebt : Bool
    abstractContractsAreCertifiedTheorems : Bool

canonicalGodelNamedLimitsProofDebtBoundary : GodelNamedLimitsProofDebtBoundary
canonicalGodelNamedLimitsProofDebtBoundary =
  godelNamedLimitsProofDebtBoundary true true false false
