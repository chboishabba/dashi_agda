module DASHI.ComputerScience.GodelNamedLimitsProofDebtBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Core.ProofDebtRouterExact as Debt
import DASHI.ComputerScience.GodelTuringNamedLimitsSourceStatusAtlasExact as Atlas

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
namedLimitRoute Atlas.rosserFirstIncompleteness = sourceTheoremNeedsAlignment
namedLimitRoute Atlas.hilbertBernaysDerivabilityConditions = sourceTheoremNeedsAlignment
namedLimitRoute Atlas.godelSecondIncompleteness = sourceTheoremNeedsAlignment
namedLimitRoute Atlas.lobTheorem = sourceTheoremNeedsAlignment
namedLimitRoute Atlas.tarskiUndefinability = sourceTheoremNeedsAlignment
namedLimitRoute Atlas.churchEntscheidungsproblem = sourceTheoremNeedsAlignment
namedLimitRoute Atlas.turingHaltingUndecidability = sourceTheoremNeedsAlignment
namedLimitRoute Atlas.kleeneRecursionFixedPoint = sourceTheoremNeedsAlignment
namedLimitRoute Atlas.riceTheorem = sourceTheoremNeedsAlignment
namedLimitRoute Atlas.busyBeaverNoncomputability = sourceTheoremNeedsAlignment

godelNumberingIsCertificationDebtOnly : Debt.routedDebt (namedLimitRoute Atlas.godelNumbering) ≡ Debt.certificationDebt
godelNumberingIsCertificationDebtOnly = refl
godelINeedsAlignmentBeforeCertification : Debt.routedDebt (namedLimitRoute Atlas.godelFirstIncompleteness) ≡ Debt.transcriptionDebt
godelINeedsAlignmentBeforeCertification = refl
rosserINeedsAlignmentBeforeCertification : Debt.routedDebt (namedLimitRoute Atlas.rosserFirstIncompleteness) ≡ Debt.transcriptionDebt
rosserINeedsAlignmentBeforeCertification = refl
godelIINeedsAlignmentBeforeCertification : Debt.routedDebt (namedLimitRoute Atlas.godelSecondIncompleteness) ≡ Debt.transcriptionDebt
godelIINeedsAlignmentBeforeCertification = refl
lobNeedsAlignmentBeforeCertification : Debt.routedDebt (namedLimitRoute Atlas.lobTheorem) ≡ Debt.transcriptionDebt
lobNeedsAlignmentBeforeCertification = refl
tarskiNeedsAlignmentBeforeCertification : Debt.routedDebt (namedLimitRoute Atlas.tarskiUndefinability) ≡ Debt.transcriptionDebt
tarskiNeedsAlignmentBeforeCertification = refl
turingNeedsAlignmentBeforeCertification : Debt.routedDebt (namedLimitRoute Atlas.turingHaltingUndecidability) ≡ Debt.transcriptionDebt
turingNeedsAlignmentBeforeCertification = refl
riceNeedsAlignmentBeforeCertification : Debt.routedDebt (namedLimitRoute Atlas.riceTheorem) ≡ Debt.transcriptionDebt
riceNeedsAlignmentBeforeCertification = refl
busyBeaverNeedsAlignmentBeforeCertification : Debt.routedDebt (namedLimitRoute Atlas.busyBeaverNoncomputability) ≡ Debt.transcriptionDebt
busyBeaverNeedsAlignmentBeforeCertification = refl

data SourceEstablishedMeansSourceAligned : Set where
data AbstractContractMeansTheoremCertified : Set where
data ExistingGodelNumberMeansIncompletenessClosed : Set where
data RosserRouteClosesOrdinaryGodelRoute : Set where

sourceEstablishedDoesNotMeanAligned : SourceEstablishedMeansSourceAligned → ⊥
sourceEstablishedDoesNotMeanAligned ()
abstractContractDoesNotCertifyTheorem : AbstractContractMeansTheoremCertified → ⊥
abstractContractDoesNotCertifyTheorem ()
godelNumberingDoesNotCloseIncompleteness : ExistingGodelNumberMeansIncompletenessClosed → ⊥
godelNumberingDoesNotCloseIncompleteness ()
rosserDoesNotDefinitionallyCloseOrdinaryGodel : RosserRouteClosesOrdinaryGodelRoute → ⊥
rosserDoesNotDefinitionallyCloseOrdinaryGodel ()

record GodelNamedLimitsProofDebtBoundary : Set where
  constructor godelNamedLimitsProofDebtBoundary
  field
    implementedNumberingRoutedSeparately : Bool
    theoremSourcesNeedExactAlignment : Bool
    rosserAndOrdinaryGodelRoutedSeparately : Bool
    tarskiMetadataGapClosedButTheoremAlignmentOpen : Bool
    alignmentDebtIsCertificationDebt : Bool
    abstractContractsAreCertifiedTheorems : Bool

canonicalGodelNamedLimitsProofDebtBoundary : GodelNamedLimitsProofDebtBoundary
canonicalGodelNamedLimitsProofDebtBoundary = godelNamedLimitsProofDebtBoundary true true true true false false
