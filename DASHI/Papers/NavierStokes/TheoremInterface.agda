module DASHI.Papers.NavierStokes.TheoremInterface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Papers.NavierStokes.FourLaneProofProgramExact as Program
import DASHI.Physics.Closure.NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact as R568
import DASHI.Physics.Closure.NSTriadKNDirectLeafACompilerRound572Exact as R572
import DASHI.Physics.Closure.NSTriadKNDirectResolventSignedCrossToR415Round503Exact as R503
import DASHI.Physics.Closure.NSTriadKNDirectResolventIntegratedCompanionRound500Exact as R500
import DASHI.Physics.Closure.NSTriadKNComparableOutputGramTelescopeRound209Exact as R209
import DASHI.Physics.Closure.NSTriadKNComparableOutputResidualPaymentRound211Exact as R211
import DASHI.Physics.Closure.NSTriadKNComparableConstantBandGramNoGoRound214Exact as R214
import DASHI.Physics.Closure.NSTriadKNPeriodicClayEligibilityMaxCutRound642Exact as R642
import DASHI.Physics.Closure.NSTriadKNPeriodicTwoInequalityMaxCutRound650Exact as R650

-- Historical/alternative route anchors retained deliberately. They are no
-- longer the primary paper-facing producer path, but their theorem-bearing
-- work and terminal guards remain part of the provenance record.
import DASHI.Physics.Closure.NSA6TheoremLadderBoundary as A6
import DASHI.Physics.Closure.NSA7ResidualDepletionGronwallBoundary as A7
import DASHI.Physics.Closure.NSA8FullLocalDefectMonotonicityBoundary as A8
import DASHI.Physics.Closure.NSA9CKNBKMClosureBoundary as A9
import DASHI.Physics.Closure.NSFinalStateReceipt as Final
import DASHI.Papers.NavierStokes.ClayContractRound23 as Clay23

------------------------------------------------------------------------
-- Canonical Paper-1 theorem/status interface after the 2026-09-15 A/B/C/D
-- nomenclature correction.
--
-- Programme lanes:
--   A = unforced whole-space R^3 regularity
--   B = unforced periodic T^3 regularity
--   C = forced whole-space R^3 breakdown verification/provenance
--   D = forced periodic T^3 breakdown verification/provenance
--
-- Current periodic-B Clay max-cut:
--
--   NEW / NONSTANDARD -- EXACTLY TWO
--     C1  R568 cutoff-uniform live signed-commutator spacetime payment
--     C2  physical R98 packet strict-surplus payment by literal R406,
--         with positive retained margin delta
--
--   COMPILED / SAME-OBJECT
--     C3  canonical literal H^(1/2)/H^(3/2)-type R414 slice
--     C5  retained viscosity is derived from C2's positive margin
--
--   STANDARD SOURCE INSTANTIATION
--     C4  smooth/common initial datum -> canonical dyadic critical ceiling
--     C6  scalar FTC / integration-linearity / order receipts
--     C7  periodic Sobolev-Rellich-Simon-weak-* package
--
-- R571 centered/Taylor, second-moment/six-three, Gram/P3, Bony/Schur and
-- self/external channel splits are retained as producer strategies and
-- provenance.  They are not independent terminal Clay obligations.
--
-- NOTE: the historical identifier `DirectLeafA...` is an owner name and does
-- not mean programme Lane A.
--
-- The same-output Gram/P3 route remains theorem-bearing historical provenance
-- and negative-control infrastructure. It is not erased. It is no longer the
-- primary B producer after the amplitude telescope exposed a many-to-one
-- observable map that blocks incidence-only lower separation.
------------------------------------------------------------------------

historicalAlternativeRouteStatement : String
historicalAlternativeRouteStatement =
  "Historical/alternative A1-A9 ESS/Abel-defect, Round62 Com/Schur, and same-output Gram/P3 routes are retained as dated predecessor strategies. They contributed theorem-bearing reductions, diagnostics, PSD/difference infrastructure, and negative controls. The Gram/P3 route was abandoned as the primary periodic-B producer after the exact amplitude telescope exposed a many-to-one observable map, so incidence geometry alone cannot force the uniform compressed-cell separation it required."

paperInterfaceStatement : String
paperInterfaceStatement =
  "Paper-facing NS interface: programme Lane B is the active unforced periodic T^3 construction; Lane A remains an independent unforced whole-space R^3 obligation; C/D are forced-breakdown verification/provenance lanes. The canonical periodic Clay max-cut is the R650 two-inequality cut: C1 is the live R568 cutoff-uniform signed-commutator spacetime payment; C2 is the live physical R98 packet strict-surplus payment by literal R406 with a positive retained margin. R645 derives retained viscosity from that C2 margin, so C5 is not an independent theorem. C3 is compiled same-object structure; C4/C6/C7 are standard source-instantiation layers with typed consumer boundaries. R571 centered/Taylor, second-moment/six-three, Gram/P3, Bony/Schur, DFL/DHH/core, and split self/external channels are producer strategies rather than independent Clay obligations. No B progress promotes A without a typed transfer theorem, no A progress promotes B without a typed transfer theorem, and C/D do not settle unforced A/B. No unconditional Clay Navier-Stokes or terminal promotion is made."

record NSPaperTheoremStatus : Setω where
  field
    ----------------------------------------------------------------------
    -- Four-lane programme / transfer firewall.
    ----------------------------------------------------------------------
    fourLaneProgram : Program.NSFourLaneProofProgram
    fourLaneProgramIsCanonical :
      fourLaneProgram ≡ Program.canonicalNSFourLaneProofProgram

    periodicBIsActiveConstruction : Bool
    periodicBIsActiveConstructionMatchesProgram :
      periodicBIsActiveConstruction
      ≡ Program.periodicBIsActiveConstruction Program.canonicalNSFourLaneProofProgram
    periodicBIsActiveConstructionIsTrue :
      periodicBIsActiveConstruction ≡ true

    wholeSpaceAIsIndependentObligation : Bool
    wholeSpaceAIsIndependentObligationMatchesProgram :
      wholeSpaceAIsIndependentObligation
      ≡ Program.wholeSpaceAIsIndependentObligation Program.canonicalNSFourLaneProofProgram
    wholeSpaceAIsIndependentObligationIsTrue :
      wholeSpaceAIsIndependentObligation ≡ true

    periodicBProofProgressDoesNotPromoteWholeSpaceA : Bool
    periodicBProofProgressDoesNotPromoteWholeSpaceAMatchesProgram :
      periodicBProofProgressDoesNotPromoteWholeSpaceA
      ≡ Program.periodicBProofProgressDoesNotPromoteWholeSpaceA Program.canonicalNSFourLaneProofProgram
    periodicBProofProgressDoesNotPromoteWholeSpaceAIsTrue :
      periodicBProofProgressDoesNotPromoteWholeSpaceA ≡ true

    wholeSpaceAProofProgressDoesNotPromotePeriodicB : Bool
    wholeSpaceAProofProgressDoesNotPromotePeriodicBMatchesProgram :
      wholeSpaceAProofProgressDoesNotPromotePeriodicB
      ≡ Program.wholeSpaceAProofProgressDoesNotPromotePeriodicB Program.canonicalNSFourLaneProofProgram
    wholeSpaceAProofProgressDoesNotPromotePeriodicBIsTrue :
      wholeSpaceAProofProgressDoesNotPromotePeriodicB ≡ true

    forcedCDDoesNotSettleUnforcedAB : Bool
    forcedCDDoesNotSettleUnforcedABMatchesProgram :
      forcedCDDoesNotSettleUnforcedAB
      ≡ Program.forcedCDDoesNotSettleUnforcedAB Program.canonicalNSFourLaneProofProgram
    forcedCDDoesNotSettleUnforcedABIsTrue :
      forcedCDDoesNotSettleUnforcedAB ≡ true

    ----------------------------------------------------------------------
    -- Modern periodic-B canonical spine.
    ----------------------------------------------------------------------
    directCompanionConstructed : Bool
    directCompanionConstructedMatchesOwner :
      directCompanionConstructed
      ≡ R500.round500IntegratedDirectCompanionWeldClosedModuloIntegrationAuthority
    directCompanionConstructedIsTrue :
      directCompanionConstructed ≡ true

    periodicBR571TaylorRealizationClosed : Bool
    periodicBR571TaylorRealizationClosedMatchesProgram :
      periodicBR571TaylorRealizationClosed
      ≡ Program.periodicBR571TaylorRealizationClosed Program.canonicalNSFourLaneProofProgram
    periodicBR571TaylorRealizationClosedIsFalse :
      periodicBR571TaylorRealizationClosed ≡ false

    periodicBSecondMomentSixThreeTransplantClosed : Bool
    periodicBSecondMomentSixThreeTransplantClosedMatchesProgram :
      periodicBSecondMomentSixThreeTransplantClosed
      ≡ Program.periodicBSecondMomentSixThreeTransplantClosed Program.canonicalNSFourLaneProofProgram
    periodicBSecondMomentSixThreeTransplantClosedIsFalse :
      periodicBSecondMomentSixThreeTransplantClosed ≡ false

    commutatorOnlySpacetimeProducerClosed : Bool
    commutatorOnlySpacetimeProducerMatchesOwner :
      commutatorOnlySpacetimeProducerClosed
      ≡ R568.round568LiveCommutatorSpacetimeBudgetClosed
    commutatorOnlySpacetimeProducerClosedIsFalse :
      commutatorOnlySpacetimeProducerClosed ≡ false

    directLeafACompilerConstructed : Bool
    directLeafACompilerConstructedMatchesOwner :
      directLeafACompilerConstructed
      ≡ R572.round572R503DirectBudgetCompilerClosedGivenReceipts
    directLeafACompilerConstructedIsTrue :
      directLeafACompilerConstructed ≡ true

    directOffDiagonalConsumerConstructed : Bool
    directOffDiagonalConsumerConstructedMatchesOwner :
      directOffDiagonalConsumerConstructed
      ≡ R503.round503ExactR500ToR415CompilerClosed
    directOffDiagonalConsumerConstructedIsTrue :
      directOffDiagonalConsumerConstructed ≡ true

    directOffDiagonalBudgetPaid : Bool
    directOffDiagonalBudgetPaidMatchesOwner :
      directOffDiagonalBudgetPaid ≡ R503.round503DirectOffDiagonalBudgetClosed
    directOffDiagonalBudgetPaidIsFalse :
      directOffDiagonalBudgetPaid ≡ false

    ----------------------------------------------------------------------
    -- Historical same-output Gram/P3 route retained append-only.
    ----------------------------------------------------------------------
    sameOutputDebtIdentityConstructed : Bool
    sameOutputDebtIdentityConstructedMatchesOwner :
      sameOutputDebtIdentityConstructed
      ≡ R209.round209OnlySameOutputComparableDebtRemains
    sameOutputDebtIdentityConstructedIsTrue :
      sameOutputDebtIdentityConstructed ≡ true

    sameOutputDebtPaymentClosed : Bool
    sameOutputDebtPaymentClosedMatchesOwner :
      sameOutputDebtPaymentClosed
      ≡ R211.round211ConcreteSameOutputResidualPaymentConstructed
    sameOutputDebtPaymentClosedIsFalse :
      sameOutputDebtPaymentClosed ≡ false

    p3SeparationProducerClosed : Bool
    p3SeparationProducerClosedMatchesPayment :
      p3SeparationProducerClosed
      ≡ R211.round211ConcreteSameOutputResidualPaymentConstructed
    p3SeparationProducerClosedIsFalse :
      p3SeparationProducerClosed ≡ false

    p3GramAttemptRetainedAsHistoricalProvenance : Bool
    p3GramAttemptRetainedAsHistoricalProvenanceMatchesProgram :
      p3GramAttemptRetainedAsHistoricalProvenance
      ≡ Program.gramP3AttemptRetainedAsHistoricalProvenance Program.canonicalNSFourLaneProofProgram
    p3GramAttemptRetainedAsHistoricalProvenanceIsTrue :
      p3GramAttemptRetainedAsHistoricalProvenance ≡ true

    p3GramAttemptAbandonedAsPrimaryRoute : Bool
    p3GramAttemptAbandonedAsPrimaryRouteMatchesProgram :
      p3GramAttemptAbandonedAsPrimaryRoute
      ≡ Program.gramP3AttemptAbandonedAsPrimaryRoute Program.canonicalNSFourLaneProofProgram
    p3GramAttemptAbandonedAsPrimaryRouteIsTrue :
      p3GramAttemptAbandonedAsPrimaryRoute ≡ true

    constantBandLocalizationAlonePaysDebt : Bool
    constantBandLocalizationAlonePaysDebtMatchesNoGo :
      constantBandLocalizationAlonePaysDebt
      ≡ R214.round214ConstantShellBandAlonePaysGramDebt
    constantBandLocalizationAlonePaysDebtIsFalse :
      constantBandLocalizationAlonePaysDebt ≡ false

    ----------------------------------------------------------------------
    -- Earlier historical provenance retained rather than rewritten away.
    ----------------------------------------------------------------------
    historicalAlternativeRoute : String
    historicalAlternativeRouteIsCanonical :
      historicalAlternativeRoute ≡ historicalAlternativeRouteStatement

    historicalA1A9Retained : Bool
    historicalA1A9RetainedIsTrue :
      historicalA1A9Retained ≡ true

    historicalRound62Retained : Bool
    historicalRound62RetainedIsTrue :
      historicalRound62Retained ≡ true

    historicalA6TheoremReceipt : A6.NSA6TheoremLadderBoundary
    historicalA6TheoremReceiptIsCanonical :
      historicalA6TheoremReceipt ≡ A6.canonicalNSA6TheoremLadderBoundary

    historicalA9ClosureReceipt : A9.NSA9CKNBKMClosureBoundary
    historicalA9ClosureReceiptIsCanonical :
      historicalA9ClosureReceipt ≡ A9.canonicalNSA9CKNBKMClosureBoundary

    historicalClayContract : Clay23.NSClayContractRound23Status
    historicalClayContractIsCanonical :
      historicalClayContract ≡ Clay23.canonicalNSClayContractRound23Status

    finalStateReceipt : Final.NSFinalStateReceipt
    finalStateReceiptIsCanonical :
      Final.statement finalStateReceipt ≡ Final.nsFinalStateStatement

    ----------------------------------------------------------------------
    -- Terminal claim guard.
    ----------------------------------------------------------------------
    clayTerminalPromotion : Bool
    clayTerminalPromotionMatchesModernOwner :
      clayTerminalPromotion ≡ R568.round568ClayPromotion
    clayTerminalPromotionIsFalse :
      clayTerminalPromotion ≡ false

    statement : String
    statementIsCanonical :
      statement ≡ paperInterfaceStatement

canonicalNSPaperTheoremStatus : NSPaperTheoremStatus
canonicalNSPaperTheoremStatus =
  record
    { fourLaneProgram = Program.canonicalNSFourLaneProofProgram
    ; fourLaneProgramIsCanonical = refl
    ; periodicBIsActiveConstruction =
        Program.periodicBIsActiveConstruction Program.canonicalNSFourLaneProofProgram
    ; periodicBIsActiveConstructionMatchesProgram = refl
    ; periodicBIsActiveConstructionIsTrue = refl
    ; wholeSpaceAIsIndependentObligation =
        Program.wholeSpaceAIsIndependentObligation Program.canonicalNSFourLaneProofProgram
    ; wholeSpaceAIsIndependentObligationMatchesProgram = refl
    ; wholeSpaceAIsIndependentObligationIsTrue = refl
    ; periodicBProofProgressDoesNotPromoteWholeSpaceA =
        Program.periodicBProofProgressDoesNotPromoteWholeSpaceA Program.canonicalNSFourLaneProofProgram
    ; periodicBProofProgressDoesNotPromoteWholeSpaceAMatchesProgram = refl
    ; periodicBProofProgressDoesNotPromoteWholeSpaceAIsTrue = refl
    ; wholeSpaceAProofProgressDoesNotPromotePeriodicB =
        Program.wholeSpaceAProofProgressDoesNotPromotePeriodicB Program.canonicalNSFourLaneProofProgram
    ; wholeSpaceAProofProgressDoesNotPromotePeriodicBMatchesProgram = refl
    ; wholeSpaceAProofProgressDoesNotPromotePeriodicBIsTrue = refl
    ; forcedCDDoesNotSettleUnforcedAB =
        Program.forcedCDDoesNotSettleUnforcedAB Program.canonicalNSFourLaneProofProgram
    ; forcedCDDoesNotSettleUnforcedABMatchesProgram = refl
    ; forcedCDDoesNotSettleUnforcedABIsTrue = refl
    ; directCompanionConstructed =
        R500.round500IntegratedDirectCompanionWeldClosedModuloIntegrationAuthority
    ; directCompanionConstructedMatchesOwner = refl
    ; directCompanionConstructedIsTrue = refl
    ; periodicBR571TaylorRealizationClosed =
        Program.periodicBR571TaylorRealizationClosed Program.canonicalNSFourLaneProofProgram
    ; periodicBR571TaylorRealizationClosedMatchesProgram = refl
    ; periodicBR571TaylorRealizationClosedIsFalse = refl
    ; periodicBSecondMomentSixThreeTransplantClosed =
        Program.periodicBSecondMomentSixThreeTransplantClosed Program.canonicalNSFourLaneProofProgram
    ; periodicBSecondMomentSixThreeTransplantClosedMatchesProgram = refl
    ; periodicBSecondMomentSixThreeTransplantClosedIsFalse = refl
    ; commutatorOnlySpacetimeProducerClosed =
        R568.round568LiveCommutatorSpacetimeBudgetClosed
    ; commutatorOnlySpacetimeProducerMatchesOwner = refl
    ; commutatorOnlySpacetimeProducerClosedIsFalse = refl
    ; directLeafACompilerConstructed =
        R572.round572R503DirectBudgetCompilerClosedGivenReceipts
    ; directLeafACompilerConstructedMatchesOwner = refl
    ; directLeafACompilerConstructedIsTrue = refl
    ; directOffDiagonalConsumerConstructed =
        R503.round503ExactR500ToR415CompilerClosed
    ; directOffDiagonalConsumerConstructedMatchesOwner = refl
    ; directOffDiagonalConsumerConstructedIsTrue = refl
    ; directOffDiagonalBudgetPaid = R503.round503DirectOffDiagonalBudgetClosed
    ; directOffDiagonalBudgetPaidMatchesOwner = refl
    ; directOffDiagonalBudgetPaidIsFalse = refl
    ; sameOutputDebtIdentityConstructed =
        R209.round209OnlySameOutputComparableDebtRemains
    ; sameOutputDebtIdentityConstructedMatchesOwner = refl
    ; sameOutputDebtIdentityConstructedIsTrue = refl
    ; sameOutputDebtPaymentClosed =
        R211.round211ConcreteSameOutputResidualPaymentConstructed
    ; sameOutputDebtPaymentClosedMatchesOwner = refl
    ; sameOutputDebtPaymentClosedIsFalse = refl
    ; p3SeparationProducerClosed =
        R211.round211ConcreteSameOutputResidualPaymentConstructed
    ; p3SeparationProducerClosedMatchesPayment = refl
    ; p3SeparationProducerClosedIsFalse = refl
    ; p3GramAttemptRetainedAsHistoricalProvenance =
        Program.gramP3AttemptRetainedAsHistoricalProvenance Program.canonicalNSFourLaneProofProgram
    ; p3GramAttemptRetainedAsHistoricalProvenanceMatchesProgram = refl
    ; p3GramAttemptRetainedAsHistoricalProvenanceIsTrue = refl
    ; p3GramAttemptAbandonedAsPrimaryRoute =
        Program.gramP3AttemptAbandonedAsPrimaryRoute Program.canonicalNSFourLaneProofProgram
    ; p3GramAttemptAbandonedAsPrimaryRouteMatchesProgram = refl
    ; p3GramAttemptAbandonedAsPrimaryRouteIsTrue = refl
    ; constantBandLocalizationAlonePaysDebt =
        R214.round214ConstantShellBandAlonePaysGramDebt
    ; constantBandLocalizationAlonePaysDebtMatchesNoGo = refl
    ; constantBandLocalizationAlonePaysDebtIsFalse = refl
    ; historicalAlternativeRoute = historicalAlternativeRouteStatement
    ; historicalAlternativeRouteIsCanonical = refl
    ; historicalA1A9Retained = true
    ; historicalA1A9RetainedIsTrue = refl
    ; historicalRound62Retained = true
    ; historicalRound62RetainedIsTrue = refl
    ; historicalA6TheoremReceipt = A6.canonicalNSA6TheoremLadderBoundary
    ; historicalA6TheoremReceiptIsCanonical = refl
    ; historicalA9ClosureReceipt = A9.canonicalNSA9CKNBKMClosureBoundary
    ; historicalA9ClosureReceiptIsCanonical = refl
    ; historicalClayContract = Clay23.canonicalNSClayContractRound23Status
    ; historicalClayContractIsCanonical = refl
    ; finalStateReceipt = Final.canonicalNSFinalStateReceipt
    ; finalStateReceiptIsCanonical = refl
    ; clayTerminalPromotion = R568.round568ClayPromotion
    ; clayTerminalPromotionMatchesModernOwner = refl
    ; clayTerminalPromotionIsFalse = refl
    ; statement = paperInterfaceStatement
    ; statementIsCanonical = refl
    }

------------------------------------------------------------------------
-- Modern periodic Clay max-cut aliases (R642).
------------------------------------------------------------------------

periodicClayMaxCutC1Closed : Bool
periodicClayMaxCutC1Closed = R642.round642C1R568SignedPaymentClosed

periodicClayMaxCutC2StillProofBearing : Bool
periodicClayMaxCutC2StillProofBearing =
  R642.round642C2PhaseSensitiveProductionStillProofBearing

periodicClayMaxCutC2StrictMarginNormalFormAvailable : Bool
periodicClayMaxCutC2StrictMarginNormalFormAvailable =
  R642.round642C2StrictMarginNormalFormAvailable

periodicClayMaxCutC2StrictMarginAlsoPaysC5 : Bool
periodicClayMaxCutC2StrictMarginAlsoPaysC5 =
  R642.round642C2StrictMarginAlsoPaysC5

periodicClayMaxCutC2LiteralRadialSurplusNormalizationClosed : Bool
periodicClayMaxCutC2LiteralRadialSurplusNormalizationClosed =
  R642.round642C2LiteralRadialSurplusNormalizationClosed

periodicClayMaxCutC2RemainingLeafCanBeOneRadialSurplusPayment : Bool
periodicClayMaxCutC2RemainingLeafCanBeOneRadialSurplusPayment =
  R642.round642C2RemainingLeafCanBeOneRadialSurplusPayment

periodicClayMaxCutC2PhysicalPacketSurplusCompilerAvailable : Bool
periodicClayMaxCutC2PhysicalPacketSurplusCompilerAvailable =
  R642.round642C2PhysicalPacketSurplusCompilerAvailable

periodicClayMaxCutC2RemainingLeafCanBePhysicalPacketR406Payment : Bool
periodicClayMaxCutC2RemainingLeafCanBePhysicalPacketR406Payment =
  R642.round642C2RemainingLeafCanBePhysicalPacketR406Payment

periodicClayMaxCutExactlyTwoNewNSAnalyticLeaves : Bool
periodicClayMaxCutExactlyTwoNewNSAnalyticLeaves =
  R650.round650ExactlyTwoNewNSAnalyticLeaves

periodicClayMaxCutUniversalViscosityOnlyC2ShortcutAdmissible : Bool
periodicClayMaxCutUniversalViscosityOnlyC2ShortcutAdmissible =
  R650.round650UniversalViscosityOnlyC2ShortcutAdmissible

periodicClayMaxCutC2MustRetainScaleChangingMechanism : Bool
periodicClayMaxCutC2MustRetainScaleChangingMechanism =
  R650.round650C2MustRetainScaleChangingMechanism

periodicClayMaxCutQuantitativeStressHarnessInstalled : Bool
periodicClayMaxCutQuantitativeStressHarnessInstalled =
  R650.round650QuantitativeStressHarnessInstalled

periodicClayMaxCutC1R406PointwiseCouplingClosed : Bool
periodicClayMaxCutC1R406PointwiseCouplingClosed =
  R650.round650C1R406PointwiseCouplingClosed

periodicClayMaxCutC1R406IntegratedCouplingClosed : Bool
periodicClayMaxCutC1R406IntegratedCouplingClosed =
  R650.round650C1R406IntegratedCouplingClosed

periodicClayMaxCutC1AndC2ShareLiteralR406Currency : Bool
periodicClayMaxCutC1AndC2ShareLiteralR406Currency =
  R650.round650C1AndC2ShareLiteralR406Currency

periodicClayMaxCutC2CoupledSandwichEquivalent : Bool
periodicClayMaxCutC2CoupledSandwichEquivalent =
  R650.round650C2CoupledSandwichEquivalent

periodicClayMaxCutC1AndC2SearchableAsLiteralSandwich : Bool
periodicClayMaxCutC1AndC2SearchableAsLiteralSandwich =
  R650.round650C1AndC2SearchableAsLiteralSandwich

periodicClayMaxCutThirdAnalyticLeafIntroducedBySandwich : Bool
periodicClayMaxCutThirdAnalyticLeafIntroducedBySandwich =
  R650.round650ThirdAnalyticLeafIntroducedBySandwich

periodicClayMaxCutC2UpperCollarRemoteSplitClosed : Bool
periodicClayMaxCutC2UpperCollarRemoteSplitClosed =
  R650.round650C2UpperCollarRemoteSplitClosed

periodicClayMaxCutC2LowRemoteSpectralDatumConstructed : Bool
periodicClayMaxCutC2LowRemoteSpectralDatumConstructed =
  R650.round650C2LowRemoteSpectralDatumConstructed

periodicClayMaxCutC2RemoteSpectralCrossCoercivityConstructed : Bool
periodicClayMaxCutC2RemoteSpectralCrossCoercivityConstructed =
  R650.round650C2RemoteSpectralCrossCoercivityConstructed

periodicClayMaxCutC2RemoteCoercivityPaysRemoteBoundaryFlux : Bool
periodicClayMaxCutC2RemoteCoercivityPaysRemoteBoundaryFlux =
  R650.round650C2RemoteCoercivityPaysRemoteBoundaryFlux

periodicClayMaxCutC2SignedCollarPaymentClosed : Bool
periodicClayMaxCutC2SignedCollarPaymentClosed =
  R650.round650C2SignedCollarPaymentClosed

periodicClayMaxCutC2LowComplementCrossReducedToCollar : Bool
periodicClayMaxCutC2LowComplementCrossReducedToCollar =
  R650.round650C2LowComplementCrossReducedToCollar

periodicClayMaxCutC2RemoteSpectralCrossDeletedFromRatioHardTerm : Bool
periodicClayMaxCutC2RemoteSpectralCrossDeletedFromRatioHardTerm =
  R650.round650C2RemoteSpectralCrossDeletedFromRatioHardTerm

periodicClayMaxCutC2RemoteBoundaryFluxStillUnpaid : Bool
periodicClayMaxCutC2RemoteBoundaryFluxStillUnpaid =
  R650.round650C2RemoteBoundaryFluxStillUnpaid

periodicClayMaxCutC2EuclideanCollarRefinementClosed : Bool
periodicClayMaxCutC2EuclideanCollarRefinementClosed =
  R650.round650C2EuclideanCollarRefinementClosed

periodicClayMaxCutC2PhysicalBoundaryFluxCollarRefinementClosed : Bool
periodicClayMaxCutC2PhysicalBoundaryFluxCollarRefinementClosed =
  R650.round650C2PhysicalBoundaryFluxCollarRefinementClosed

periodicClayMaxCutC2GoodCollarSpectralCrossNonpositive : Bool
periodicClayMaxCutC2GoodCollarSpectralCrossNonpositive =
  R650.round650C2GoodCollarSpectralCrossNonpositive

periodicClayMaxCutC2FullCrossReducedToBadLowRadiusCollar : Bool
periodicClayMaxCutC2FullCrossReducedToBadLowRadiusCollar =
  R650.round650C2FullCrossReducedToBadLowRadiusCollar

periodicClayMaxCutC2BadLowRadiusCollarPaymentClosed : Bool
periodicClayMaxCutC2BadLowRadiusCollarPaymentClosed =
  R650.round650C2BadLowRadiusCollarPaymentClosed

periodicClayMaxCutC2BadCollarPureSpectralOrderingAdmissible : Bool
periodicClayMaxCutC2BadCollarPureSpectralOrderingAdmissible =
  R650.round650C2BadCollarPureSpectralOrderingAdmissible

periodicClayMaxCutC2BadCollarNeedsSignedNonlinearOrStateDependentInput : Bool
periodicClayMaxCutC2BadCollarNeedsSignedNonlinearOrStateDependentInput =
  R650.round650C2BadCollarNeedsSignedNonlinearOrStateDependentInput

periodicClayMaxCutC2BadCollarUsesSameHeatNestedR98OuterCarrier : Bool
periodicClayMaxCutC2BadCollarUsesSameHeatNestedR98OuterCarrier =
  R650.round650C2BadCollarUsesSameHeatNestedR98OuterCarrier

periodicClayMaxCutC2BadCollarActiveFibreIsUnweightedCommutator : Bool
periodicClayMaxCutC2BadCollarActiveFibreIsUnweightedCommutator =
  R650.round650C2BadCollarActiveFibreIsUnweightedCommutator

periodicClayMaxCutC2BadCollarQuantitativeFixedOutputPaymentClosed : Bool
periodicClayMaxCutC2BadCollarQuantitativeFixedOutputPaymentClosed =
  R650.round650C2BadCollarQuantitativeFixedOutputPaymentClosed

periodicClayMaxCutC2CriticalEnergyGrowthNormalFormAvailable : Bool
periodicClayMaxCutC2CriticalEnergyGrowthNormalFormAvailable =
  R650.round650C2CriticalEnergyGrowthNormalFormAvailable

periodicClayMaxCutC2EnergyGrowthMarginPaymentCompilesToC2 : Bool
periodicClayMaxCutC2EnergyGrowthMarginPaymentCompilesToC2 =
  R650.round650C2EnergyGrowthMarginPaymentCompilesToC2

periodicClayMaxCutC2ExactlyEquivalentToEnergyGrowthMarginPayment : Bool
periodicClayMaxCutC2ExactlyEquivalentToEnergyGrowthMarginPayment =
  R650.round650C2ExactlyEquivalentToEnergyGrowthMarginPayment

periodicClayMaxCutC2EnergyGrowthMarginPaymentClosed : Bool
periodicClayMaxCutC2EnergyGrowthMarginPaymentClosed =
  R650.round650C2EnergyGrowthMarginPaymentClosed


periodicClayMaxCutC2ActualWeightedBadCollarPairDifferenceFormClosed : Bool
periodicClayMaxCutC2ActualWeightedBadCollarPairDifferenceFormClosed =
  R650.round650C2ActualWeightedBadCollarCommutatorPairDifferenceFormClosed

periodicClayMaxCutC2WholeBadCollarFibreIsComparableOnlyP3Carrier : Bool
periodicClayMaxCutC2WholeBadCollarFibreIsComparableOnlyP3Carrier =
  R650.round650C2WholeBadCollarFibreIsComparableOnlyP3Carrier

periodicClayMaxCutC2BadCollarSpacetimePairDifferenceNormalFormClosed : Bool
periodicClayMaxCutC2BadCollarSpacetimePairDifferenceNormalFormClosed =
  R650.round650C2BadCollarSpacetimePairDifferenceNormalFormClosed

periodicClayMaxCutC2BadCollarEndpointTangentRemovedModuloStandardCalculus : Bool
periodicClayMaxCutC2BadCollarEndpointTangentRemovedModuloStandardCalculus =
  R650.round650C2BadCollarEndpointTangentRemovedModuloStandardCalculus

periodicClayMaxCutC2FullFibrePairDifferenceM2PaymentClosed : Bool
periodicClayMaxCutC2FullFibrePairDifferenceM2PaymentClosed =
  R650.round650C2FullFibrePairDifferenceM2PaymentClosed

periodicClayMaxCutC2PairDifferenceM2AddsCardinalityTax : Bool
periodicClayMaxCutC2PairDifferenceM2AddsCardinalityTax =
  R650.round650C2PairDifferenceM2AddsCardinalityTax

periodicClayMaxCutC2LivePairDifferenceM2PaymentClosed : Bool
periodicClayMaxCutC2LivePairDifferenceM2PaymentClosed =
  R650.round650C2LivePairDifferenceM2PaymentClosed

periodicClayMaxCutC2LiveBadCollarResidualReducedToSelfRatePlusM2 : Bool
periodicClayMaxCutC2LiveBadCollarResidualReducedToSelfRatePlusM2 =
  R650.round650C2LiveBadCollarResidualReducedToSelfRatePlusM2

periodicClayMaxCutC2LiveSpacetimeM2ReductionGivenIntegrationOrder : Bool
periodicClayMaxCutC2LiveSpacetimeM2ReductionGivenIntegrationOrder =
  R650.round650C2LiveSpacetimeM2ReductionGivenIntegrationOrder

periodicClayMaxCutC2SelfRatePlusM2CutoffUniformPaymentClosed : Bool
periodicClayMaxCutC2SelfRatePlusM2CutoffUniformPaymentClosed =
  R650.round650C2SelfRatePlusM2CutoffUniformPaymentClosed


periodicClayMaxCutC2BadCollarResidualWeightedWorkIdentityClosed : Bool
periodicClayMaxCutC2BadCollarResidualWeightedWorkIdentityClosed =
  R650.round650C2BadCollarResidualWeightedWorkIdentityClosed

periodicClayMaxCutC2BadCollarSpacetimeWeightedWorkIdentityClosed : Bool
periodicClayMaxCutC2BadCollarSpacetimeWeightedWorkIdentityClosed =
  R650.round650C2BadCollarSpacetimeWeightedWorkIdentityClosed

periodicClayMaxCutC2SelfRateIndependentAnalyticLeaf : Bool
periodicClayMaxCutC2SelfRateIndependentAnalyticLeaf =
  R650.round650C2SelfRateIndependentAnalyticLeaf

periodicClayMaxCutC2M2RequiredForCanonicalBadCollarRoute : Bool
periodicClayMaxCutC2M2RequiredForCanonicalBadCollarRoute =
  R650.round650C2M2RequiredForCanonicalBadCollarRoute

periodicClayMaxCutC2BadCollarRateWeightedKernelIdentityClosed : Bool
periodicClayMaxCutC2BadCollarRateWeightedKernelIdentityClosed =
  R650.round650C2BadCollarRateWeightedKernelIdentityClosed

periodicClayMaxCutC2BadCollarSpacetimeRateWeightedKernelIdentityClosed : Bool
periodicClayMaxCutC2BadCollarSpacetimeRateWeightedKernelIdentityClosed =
  R650.round650C2BadCollarSpacetimeRateWeightedKernelIdentityClosed

periodicClayMaxCutC2BadCollarRateWeightedKernelPaymentClosed : Bool
periodicClayMaxCutC2BadCollarRateWeightedKernelPaymentClosed =
  R650.round650C2BadCollarRateWeightedKernelPaymentClosed


periodicClayMaxCutC2BadCollarOnR598MismatchCarrier : Bool
periodicClayMaxCutC2BadCollarOnR598MismatchCarrier =
  R650.round650C2BadCollarOnR598MismatchCarrier

periodicClayMaxCutC2C1ShareRateWeightedKernelVocabulary : Bool
periodicClayMaxCutC2C1ShareRateWeightedKernelVocabulary =
  R650.round650C2C1ShareRateWeightedKernelVocabulary

periodicClayMaxCutC2R598MismatchPaid : Bool
periodicClayMaxCutC2R598MismatchPaid =
  R650.round650C2R598MismatchPaid

periodicClayMaxCutC2BadCollarMismatchSelfExternalSplitClosed : Bool
periodicClayMaxCutC2BadCollarMismatchSelfExternalSplitClosed =
  R650.round650C2BadCollarMismatchSelfExternalSplitClosed

periodicClayMaxCutC2BadCollarSelectedSelfMismatchPaid : Bool
periodicClayMaxCutC2BadCollarSelectedSelfMismatchPaid =
  R650.round650C2BadCollarSelectedSelfMismatchPaid

periodicClayMaxCutC2BadCollarExternalNetworkContributionPaid : Bool
periodicClayMaxCutC2BadCollarExternalNetworkContributionPaid =
  R650.round650C2BadCollarExternalNetworkContributionPaid

periodicClayMaxCutC2UniversalScaleFreeForcingA3IdentityAdmissible : Bool
periodicClayMaxCutC2UniversalScaleFreeForcingA3IdentityAdmissible =
  R650.round650C2UniversalScaleFreeForcingA3IdentityAdmissible

periodicClayMaxCutC2BadCollarResidualA3ComplementIdentityClosed : Bool
periodicClayMaxCutC2BadCollarResidualA3ComplementIdentityClosed =
  R650.round650C2BadCollarResidualA3ComplementIdentityClosed

periodicClayMaxCutC2BadCollarSpacetimeResidualA3ComplementIdentityClosed : Bool
periodicClayMaxCutC2BadCollarSpacetimeResidualA3ComplementIdentityClosed =
  R650.round650C2BadCollarSpacetimeResidualA3ComplementIdentityClosed

periodicClayMaxCutC2A3UpperPaymentDirectlyPaysBadCollarResidual : Bool
periodicClayMaxCutC2A3UpperPaymentDirectlyPaysBadCollarResidual =
  R650.round650C2A3UpperPaymentDirectlyPaysBadCollarResidual

periodicClayMaxCutC2ExternalNetworkOnLiteralResidualFullSquare : Bool
periodicClayMaxCutC2ExternalNetworkOnLiteralResidualFullSquare =
  R650.round650C2ExternalNetworkOnLiteralResidualFullSquare

periodicClayMaxCutC2ExternalResidualFullSquareRequiresMembershipAuthority : Bool
periodicClayMaxCutC2ExternalResidualFullSquareRequiresMembershipAuthority =
  R650.round650C2ExternalResidualFullSquareRequiresMembershipAuthority

periodicClayMaxCutC2ExternalNetworkResidualFullSquarePaymentClosed : Bool
periodicClayMaxCutC2ExternalNetworkResidualFullSquarePaymentClosed =
  R650.round650C2ExternalNetworkResidualFullSquarePaymentClosed

periodicClayMaxCutC2CanonicalExternalNetworkFullSquareClosed : Bool
periodicClayMaxCutC2CanonicalExternalNetworkFullSquareClosed =
  R650.round650C2CanonicalExternalNetworkFullSquareClosed

periodicClayMaxCutC2CanonicalExternalNetworkRequiresLegacyR112WitnessFamily : Bool
periodicClayMaxCutC2CanonicalExternalNetworkRequiresLegacyR112WitnessFamily =
  R650.round650C2CanonicalExternalNetworkRequiresLegacyR112WitnessFamily

periodicClayMaxCutC2CanonicalExternalNetworkRequiresGlobalNonfixedness : Bool
periodicClayMaxCutC2CanonicalExternalNetworkRequiresGlobalNonfixedness =
  R650.round650C2CanonicalExternalNetworkRequiresGlobalNonfixedness

periodicClayMaxCutC2CanonicalExternalNetworkPreservesFixedOrbitCorrection : Bool
periodicClayMaxCutC2CanonicalExternalNetworkPreservesFixedOrbitCorrection =
  R650.round650C2CanonicalExternalNetworkPreservesFixedOrbitCorrection

periodicClayMaxCutC2CanonicalExternalNetworkPaymentClosed : Bool
periodicClayMaxCutC2CanonicalExternalNetworkPaymentClosed =
  R650.round650C2CanonicalExternalNetworkPaymentClosed

periodicClayMaxCutC2WeightedExternalProductRuleCommutatorClosed : Bool
periodicClayMaxCutC2WeightedExternalProductRuleCommutatorClosed =
  R650.round650C2WeightedExternalProductRuleCommutatorClosed

periodicClayMaxCutC2RawTotalExternalWeldOnPNonzeroClosed : Bool
periodicClayMaxCutC2RawTotalExternalWeldOnPNonzeroClosed =
  R650.round650C2RawTotalExternalWeldOnPNonzeroClosed

periodicClayMaxCutC2RawTotalNestedWeldOnPNonzeroClosed : Bool
periodicClayMaxCutC2RawTotalNestedWeldOnPNonzeroClosed =
  R650.round650C2RawTotalNestedWeldOnPNonzeroClosed

periodicClayMaxCutC2ExternalZeroBranchMayBeErasedGlobally : Bool
periodicClayMaxCutC2ExternalZeroBranchMayBeErasedGlobally =
  R650.round650C2ExternalZeroBranchMayBeErasedGlobally

periodicClayMaxCutC2R606ExternalFoldTotalizesThroughR630 : Bool
periodicClayMaxCutC2R606ExternalFoldTotalizesThroughR630 =
  R650.round650C2R606ExternalFoldTotalizesThroughR630

periodicClayMaxCutC2ExternalPZeroBranchRetainedExplicitly : Bool
periodicClayMaxCutC2ExternalPZeroBranchRetainedExplicitly =
  R650.round650C2ExternalPZeroBranchRetainedExplicitly

periodicClayMaxCutC2ExternalPZeroDefectProvedZero : Bool
periodicClayMaxCutC2ExternalPZeroDefectProvedZero =
  R650.round650C2ExternalPZeroDefectProvedZero

periodicClayMaxCutC2R606ExternalFoldEqualsR630WithoutDefect : Bool
periodicClayMaxCutC2R606ExternalFoldEqualsR630WithoutDefect =
  R650.round650C2R606ExternalFoldEqualsR630WithoutDefect

periodicClayMaxCutC2ExternalPZeroForcingEliminated : Bool
periodicClayMaxCutC2ExternalPZeroForcingEliminated =
  R650.round650C2ExternalPZeroForcingEliminated

periodicClayMaxCutC2ExternalSignedPaymentStillOpenAfterTotalization : Bool
periodicClayMaxCutC2ExternalSignedPaymentStillOpenAfterTotalization =
  R650.round650C2ExternalSignedPaymentStillOpenAfterTotalization

periodicClayMaxCutC2R606ExternalSpectatorRowToR631Closed : Bool
periodicClayMaxCutC2R606ExternalSpectatorRowToR631Closed =
  R650.round650C2R606ExternalSpectatorRowToR631Closed

periodicClayMaxCutC2R606ExternalFullSquareToCanonicalRowsClosed : Bool
periodicClayMaxCutC2R606ExternalFullSquareToCanonicalRowsClosed =
  R650.round650C2R606ExternalFullSquareToCanonicalRowsClosed

periodicClayMaxCutC2ExternalFullSquareSignedPaymentClosed : Bool
periodicClayMaxCutC2ExternalFullSquareSignedPaymentClosed =
  R650.round650C2ExternalFullSquareSignedPaymentClosed

periodicClayMaxCutC2R606ExternalFullSquareOnR636HelicityRows : Bool
periodicClayMaxCutC2R606ExternalFullSquareOnR636HelicityRows =
  R650.round650C2R606ExternalFullSquareOnR636HelicityRows

periodicClayMaxCutC2R607RateMultiplierPreservedExactly : Bool
periodicClayMaxCutC2R607RateMultiplierPreservedExactly =
  R650.round650C2R607RateMultiplierPreservedExactly

periodicClayMaxCutC2R607ExternalNetworkOnRateWeightedR637Carrier : Bool
periodicClayMaxCutC2R607ExternalNetworkOnRateWeightedR637Carrier =
  R650.round650C2R607ExternalNetworkOnRateWeightedR637Carrier

periodicClayMaxCutC2CombinedHelicityTangentCarrierClosed : Bool
periodicClayMaxCutC2CombinedHelicityTangentCarrierClosed =
  R650.round650C2CombinedHelicityTangentCarrierClosed

periodicClayMaxCutC2CombinedHelicityTangentCollapsesToSelfDiscrepancy : Bool
periodicClayMaxCutC2CombinedHelicityTangentCollapsesToSelfDiscrepancy =
  R650.round650C2CombinedHelicityTangentCollapsesToSelfDiscrepancy

periodicClayMaxCutC2BadCollarSingleSelfKernelMismatchClosed : Bool
periodicClayMaxCutC2BadCollarSingleSelfKernelMismatchClosed =
  R650.round650C2BadCollarSingleSelfKernelMismatchClosed

periodicClayMaxCutC2CombinedRouteReturnsToRateKernel : Bool
periodicClayMaxCutC2CombinedRouteReturnsToRateKernel =
  R650.round650C2CombinedRouteReturnsToRateKernel

periodicClayMaxCutC2CombinedRouteCreatesIndependentPaymentCoordinate : Bool
periodicClayMaxCutC2CombinedRouteCreatesIndependentPaymentCoordinate =
  R650.round650C2CombinedRouteCreatesIndependentPaymentCoordinate

periodicClayMaxCutC2RateWeightedKernelQuantitativePaymentClosedAfterCombinedRecut : Bool
periodicClayMaxCutC2RateWeightedKernelQuantitativePaymentClosedAfterCombinedRecut =
  R650.round650C2RateWeightedKernelQuantitativePaymentClosedAfterCombinedRecut

periodicClayMaxCutC2PositiveRatesAndPositiveSelfWorkForceFavorableKernelSign : Bool
periodicClayMaxCutC2PositiveRatesAndPositiveSelfWorkForceFavorableKernelSign =
  R650.round650C2PositiveRatesAndPositiveSelfWorkForceFavorableKernelSign

periodicClayMaxCutC2RateKernelNeedsAdditionalPhysicalStructure : Bool
periodicClayMaxCutC2RateKernelNeedsAdditionalPhysicalStructure =
  R650.round650C2RateKernelNeedsAdditionalPhysicalStructure

periodicClayMaxCutC2PhysicalRateKernelCrossGradientNormalFormClosed : Bool
periodicClayMaxCutC2PhysicalRateKernelCrossGradientNormalFormClosed =
  R650.round650C2PhysicalRateKernelCrossGradientNormalFormClosed

periodicClayMaxCutC2LiveResidualCrossGradientNormalFormClosed : Bool
periodicClayMaxCutC2LiveResidualCrossGradientNormalFormClosed =
  R650.round650C2LiveResidualCrossGradientNormalFormClosed

periodicClayMaxCutC2RemainingCoordinateUsesLiteralPDotQ : Bool
periodicClayMaxCutC2RemainingCoordinateUsesLiteralPDotQ =
  R650.round650C2RemainingCoordinateUsesLiteralPDotQ

periodicClayMaxCutC2CrossGradientQuantitativePaymentClosed : Bool
periodicClayMaxCutC2CrossGradientQuantitativePaymentClosed =
  R650.round650C2CrossGradientQuantitativePaymentClosed

periodicClayMaxCutC2PhysicalRateKernelVectorNormalFormClosed : Bool
periodicClayMaxCutC2PhysicalRateKernelVectorNormalFormClosed =
  R650.round650C2PhysicalRateKernelVectorNormalFormClosed

periodicClayMaxCutC2CrossGradientVectorUsesAbsoluteValue : Bool
periodicClayMaxCutC2CrossGradientVectorUsesAbsoluteValue =
  R650.round650C2CrossGradientVectorUsesAbsoluteValue

periodicClayMaxCutC2HelicalCrossGradientPaymentClosed : Bool
periodicClayMaxCutC2HelicalCrossGradientPaymentClosed =
  R650.round650C2HelicalCrossGradientPaymentClosed

periodicClayMaxCutC2RateKernelInputLaplacianCollapseClosed : Bool
periodicClayMaxCutC2RateKernelInputLaplacianCollapseClosed =
  R650.round650C2RateKernelInputLaplacianCollapseClosed

periodicClayMaxCutC2RateKernelIsCommutatorMinusTangent : Bool
periodicClayMaxCutC2RateKernelIsCommutatorMinusTangent =
  R650.round650C2RateKernelIsCommutatorMinusTangent

periodicClayMaxCutC2KernelSpacetimeIsCommutatorMinusEndpoint : Bool
periodicClayMaxCutC2KernelSpacetimeIsCommutatorMinusEndpoint =
  R650.round650C2KernelSpacetimeIsCommutatorMinusEndpoint

periodicClayMaxCutC2LocalNonlinearCurrencyMatchesCommutatorLane : Bool
periodicClayMaxCutC2LocalNonlinearCurrencyMatchesCommutatorLane =
  R650.round650C2LocalNonlinearCurrencyMatchesCommutatorLane

periodicClayMaxCutC1ResolventWeightedSquareAlreadyControlsC2Commutator : Bool
periodicClayMaxCutC1ResolventWeightedSquareAlreadyControlsC2Commutator =
  R650.round650C1ResolventWeightedSquareAlreadyControlsC2Commutator

periodicClayMaxCutC1C2RateLiftedForcingBridgeClosed : Bool
periodicClayMaxCutC1C2RateLiftedForcingBridgeClosed =
  R650.round650C1C2RateLiftedForcingBridgeClosed

periodicClayMaxCutC1UnliftedBudgetControlsRateLiftedFull : Bool
periodicClayMaxCutC1UnliftedBudgetControlsRateLiftedFull =
  R650.round650C1UnliftedBudgetControlsRateLiftedFull

periodicClayMaxCutC2CommutatorIsOneEighthRateLiftedR568 : Bool
periodicClayMaxCutC2CommutatorIsOneEighthRateLiftedR568 =
  R650.round650C2CommutatorIsOneEighthRateLiftedR568

periodicClayMaxCutC2RateLiftedMinusTangentIsEightPhysicalRateKernel : Bool
periodicClayMaxCutC2RateLiftedMinusTangentIsEightPhysicalRateKernel =
  R650.round650C2RateLiftedMinusTangentIsEightPhysicalRateKernel

periodicClayMaxCutC2SeparateRateLiftedAndTangentUpperBoundsRequired : Bool
periodicClayMaxCutC2SeparateRateLiftedAndTangentUpperBoundsRequired =
  R650.round650C2SeparateRateLiftedAndTangentUpperBoundsRequired

periodicClayMaxCutC2PreferredSignedDynamicCancellationPaymentClosed : Bool
periodicClayMaxCutC2PreferredSignedDynamicCancellationPaymentClosed =
  R650.round650C2PreferredSignedDynamicCancellationPaymentClosed

periodicClayMaxCutC2SignedRateLiftCollapseToInputLaplacianClosed : Bool
periodicClayMaxCutC2SignedRateLiftCollapseToInputLaplacianClosed =
  R650.round650C2SignedRateLiftCollapseToInputLaplacianClosed

periodicClayMaxCutC2SignedRateLiftSpacetimePaymentClosed : Bool
periodicClayMaxCutC2SignedRateLiftSpacetimePaymentClosed =
  R650.round650C2SignedRateLiftSpacetimePaymentClosed

periodicClayMaxCutC1UnliftedBudgetControlsSignedRateLiftCancellation : Bool
periodicClayMaxCutC1UnliftedBudgetControlsSignedRateLiftCancellation =
  R650.round650C1UnliftedBudgetControlsSignedRateLiftCancellation

periodicClayMaxCutSignedRateLiftGlobalizedBeforeEstimate : Bool
periodicClayMaxCutSignedRateLiftGlobalizedBeforeEstimate =
  R650.round650SignedRateLiftGlobalizedBeforeEstimate

periodicClayMaxCutSignedRateLiftIntegratedOnlyAfterGlobalOutputSum : Bool
periodicClayMaxCutSignedRateLiftIntegratedOnlyAfterGlobalOutputSum =
  R650.round650SignedRateLiftIntegratedOnlyAfterGlobalOutputSum

periodicClayMaxCutGlobalInputLaplacianSpacetimePaymentClosed : Bool
periodicClayMaxCutGlobalInputLaplacianSpacetimePaymentClosed =
  R650.round650GlobalInputLaplacianSpacetimePaymentClosed

periodicClayMaxCutGlobalMixedEnergyBalanceClosed : Bool
periodicClayMaxCutGlobalMixedEnergyBalanceClosed =
  R650.round650GlobalMixedEnergyBalanceClosed

periodicClayMaxCutGlobalInputLaplacianPureDissipationByAlgebra : Bool
periodicClayMaxCutGlobalInputLaplacianPureDissipationByAlgebra =
  R650.round650GlobalInputLaplacianPureDissipationByAlgebra

periodicClayMaxCutGlobalCommutatorCancellationClosed : Bool
periodicClayMaxCutGlobalCommutatorCancellationClosed =
  R650.round650GlobalCommutatorCancellationClosed

periodicClayMaxCutGlobalCommutatorCutoffUniformPaymentClosed : Bool
periodicClayMaxCutGlobalCommutatorCutoffUniformPaymentClosed =
  R650.round650GlobalCommutatorCutoffUniformPaymentClosed

periodicClayMaxCutGlobalCommutatorLiteralPairExpansionClosed : Bool
periodicClayMaxCutGlobalCommutatorLiteralPairExpansionClosed =
  R650.round650GlobalCommutatorLiteralPairExpansionClosed

periodicClayMaxCutGlobalCommutatorOuterTriadRegroupingClosed : Bool
periodicClayMaxCutGlobalCommutatorOuterTriadRegroupingClosed =
  R650.round650GlobalCommutatorOuterTriadRegroupingClosed

periodicClayMaxCutGlobalCommutatorNonzeroCarrierCyclicClosureClosed : Bool
periodicClayMaxCutGlobalCommutatorNonzeroCarrierCyclicClosureClosed =
  R650.round650GlobalCommutatorNonzeroCarrierCyclicClosureClosed

periodicClayMaxCutGlobalCommutatorNestedTriadOrbitExpansionClosed : Bool
periodicClayMaxCutGlobalCommutatorNestedTriadOrbitExpansionClosed =
  R650.round650GlobalCommutatorNestedTriadOrbitExpansionClosed

periodicClayMaxCutGlobalCommutatorOrbitCancellationClosed : Bool
periodicClayMaxCutGlobalCommutatorOrbitCancellationClosed =
  R650.round650GlobalCommutatorOrbitCancellationClosed

periodicClayMaxCutGlobalCommutatorNestedFourHelicityExpansionClosed : Bool
periodicClayMaxCutGlobalCommutatorNestedFourHelicityExpansionClosed =
  R650.round650GlobalCommutatorNestedFourHelicityExpansionClosed

periodicClayMaxCutLiveGlobalCommutatorNestedFourHelicityExpansionClosed : Bool
periodicClayMaxCutLiveGlobalCommutatorNestedFourHelicityExpansionClosed =
  R650.round650LiveGlobalCommutatorNestedFourHelicityExpansionClosed

periodicClayMaxCutLiveNestedExpansionNeedsNewTrajectoryHypothesis : Bool
periodicClayMaxCutLiveNestedExpansionNeedsNewTrajectoryHypothesis =
  R650.round650LiveNestedExpansionNeedsNewTrajectoryHypothesis

periodicClayMaxCutNonzeroSelectionMovedToCompleteTriadMask : Bool
periodicClayMaxCutNonzeroSelectionMovedToCompleteTriadMask =
  R650.round650NonzeroSelectionMovedToCompleteTriadMask

periodicClayMaxCutCompleteTriadOrbitResidueEqualsThreeCoherentCommutator : Bool
periodicClayMaxCutCompleteTriadOrbitResidueEqualsThreeCoherentCommutator =
  R650.round650CompleteTriadOrbitResidueEqualsThreeCoherentCommutator

periodicClayMaxCutCompleteTriadOrbitResidueSignedPaymentClosed : Bool
periodicClayMaxCutCompleteTriadOrbitResidueSignedPaymentClosed =
  R650.round650CompleteTriadOrbitResidueSignedPaymentClosed

periodicClayMaxCutIntegratedTriadOrbitResidueIsThreeR691Commutator : Bool
periodicClayMaxCutIntegratedTriadOrbitResidueIsThreeR691Commutator =
  R650.round650IntegratedTriadOrbitResidueIsThreeR691Commutator

periodicClayMaxCutCutoffUniformIntegratedTriadOrbitResiduePaymentClosed : Bool
periodicClayMaxCutCutoffUniformIntegratedTriadOrbitResiduePaymentClosed =
  R650.round650CutoffUniformIntegratedTriadOrbitResiduePaymentClosed

periodicClayMaxCutTriadOrbitR568R406ConsumerAttachmentClosed : Bool
periodicClayMaxCutTriadOrbitR568R406ConsumerAttachmentClosed =
  R650.round650TriadOrbitR568R406ConsumerAttachmentClosed

periodicClayMaxCutTriadOrbitPaymentShapeClosed : Bool
periodicClayMaxCutTriadOrbitPaymentShapeClosed =
  R650.round650ClayFacingTriadOrbitPaymentShapeClosed

periodicClayMaxCutR691EndpointUpperReducesToInitialMixedMass : Bool
periodicClayMaxCutR691EndpointUpperReducesToInitialMixedMass =
  R650.round650R691EndpointUpperReducesToInitialMixedMass

periodicClayMaxCutTriadOrbitPlusInitialCeilingPaysGlobalWeightedWork : Bool
periodicClayMaxCutTriadOrbitPlusInitialCeilingPaysGlobalWeightedWork =
  R650.round650TriadOrbitPlusInitialCeilingPaysGlobalWeightedWork

periodicClayMaxCutLiteralNestedFourHelicityOrbitExpansionClosed : Bool
periodicClayMaxCutLiteralNestedFourHelicityOrbitExpansionClosed =
  R650.round650LiteralNestedFourHelicityOrbitExpansionClosed

periodicClayMaxCutIntegratedNestedOrbitIsTwelveR691Commutator : Bool
periodicClayMaxCutIntegratedNestedOrbitIsTwelveR691Commutator =
  R650.round650IntegratedNestedOrbitIsTwelveR691Commutator

periodicClayMaxCutPaymentLivesOnFullyExpandedIncidenceKernel : Bool
periodicClayMaxCutPaymentLivesOnFullyExpandedIncidenceKernel =
  R650.round650ClayFacingPaymentLivesOnFullyExpandedIncidenceKernel

periodicClayMaxCutNestedFourHelicityOrbitPaymentClosed : Bool
periodicClayMaxCutNestedFourHelicityOrbitPaymentClosed =
  R650.round650CutoffUniformNestedFourHelicityOrbitPaymentClosed

periodicClayMaxCutNestedFourHelicityScalarCoefficientsExposed : Bool
periodicClayMaxCutNestedFourHelicityScalarCoefficientsExposed =
  R650.round650NestedFourHelicityScalarCoefficientsExposed

periodicClayMaxCutScalarCoefficientCancellationAloneClosesOrbit : Bool
periodicClayMaxCutScalarCoefficientCancellationAloneClosesOrbit =
  R650.round650NestedFourHelicityScalarCancellationAloneClosesOrbit

periodicClayMaxCutNestedOrbitPaymentClosedAfterCoefficientExposure : Bool
periodicClayMaxCutNestedOrbitPaymentClosedAfterCoefficientExposure =
  R650.round650NestedFourHelicityOrbitPaymentClosedAfterCoefficientExposure

periodicClayMaxCutC2UnweightedR637PaymentDirectlyPaysRateWeightedR607 : Bool
periodicClayMaxCutC2UnweightedR637PaymentDirectlyPaysRateWeightedR607 =
  R650.round650C2UnweightedR637PaymentDirectlyPaysRateWeightedR607

periodicClayMaxCutC2RateWeightedExternalSignedPaymentClosed : Bool
periodicClayMaxCutC2RateWeightedExternalSignedPaymentClosed =
  R650.round650C2RateWeightedExternalSignedPaymentClosed

periodicClayMaxCutC2WeightedExternalSignedPaymentClosed : Bool
periodicClayMaxCutC2WeightedExternalSignedPaymentClosed =
  R650.round650C2WeightedExternalSignedPaymentClosed

periodicClayMaxCutC3CompilerAvailable : Bool
periodicClayMaxCutC3CompilerAvailable =
  R642.round642C3CanonicalPhysicalSliceCompilerAvailable

periodicClayMaxCutC4CompilerAvailable : Bool
periodicClayMaxCutC4CompilerAvailable =
  R642.round642C4CommonInitialDatumSameObjectCompilerAvailable

periodicClayMaxCutC4CanonicalModeCoherenceCompilerAvailable : Bool
periodicClayMaxCutC4CanonicalModeCoherenceCompilerAvailable =
  R642.round642C4CanonicalR34ModeCoherenceCompilerAvailable

periodicClayMaxCutC4CanonicalDyadicCeilingAdapterAvailable : Bool
periodicClayMaxCutC4CanonicalDyadicCeilingAdapterAvailable =
  R642.round642C4CanonicalDyadicCeilingAdapterAvailable

periodicClayMaxCutC4StandardSmoothToHOneHalfSourceStillExternal : Bool
periodicClayMaxCutC4StandardSmoothToHOneHalfSourceStillExternal =
  R642.round642C4StandardSmoothToHOneHalfSourceStillExternal

periodicClayMaxCutC5Proved : Bool
periodicClayMaxCutC5Proved = R642.round642C5RetainedViscosityProved

periodicClayMaxCutC5IndependentIfC2UsesPositiveMargin : Bool
periodicClayMaxCutC5IndependentIfC2UsesPositiveMargin =
  R642.round642C5IndependentIfC2UsesPositiveMargin

periodicClayMaxCutC4StandardSourceBoundaryAvailable : Bool
periodicClayMaxCutC4StandardSourceBoundaryAvailable =
  R642.round642C4TypedStandardSourceBoundaryAvailable

periodicClayMaxCutC6ScalarFTCInstalled : Bool
periodicClayMaxCutC6ScalarFTCInstalled =
  R642.round642C6StandardScalarFTCInstalled

periodicClayMaxCutC7SimonClosed : Bool
periodicClayMaxCutC7SimonClosed =
  R642.round642C7PhysicalCriticalSobolevSimonUpgradeClosed

periodicClayMaxCutC6StandardSourceBoundaryAvailable : Bool
periodicClayMaxCutC6StandardSourceBoundaryAvailable =
  R642.round642C6TypedStandardSourceBoundaryAvailable

periodicClayMaxCutC7StandardSourceBoundaryAvailable : Bool
periodicClayMaxCutC7StandardSourceBoundaryAvailable =
  R642.round642C7TypedStandardSourceBoundaryAvailable

oldPDFB1B2B3B4Mandatory : Bool
oldPDFB1B2B3B4Mandatory = R642.round642OldPDFB1B2B3B4Mandatory

oldPDFB7DirectCovarianceEqualityMandatory : Bool
oldPDFB7DirectCovarianceEqualityMandatory =
  R642.round642OldPDFB7DirectCovarianceEqualityMandatory

periodicClayMaxCutC1ClosedIsFalse :
  periodicClayMaxCutC1Closed ≡ false
periodicClayMaxCutC1ClosedIsFalse =
  R642.round642C1R568SignedPaymentClosedIsFalse

periodicClayMaxCutC2StillProofBearingIsTrue :
  periodicClayMaxCutC2StillProofBearing ≡ true
periodicClayMaxCutC2StillProofBearingIsTrue =
  R642.round642C2PhaseSensitiveProductionStillProofBearingIsTrue

oldPDFB1B2B3B4MandatoryIsFalse :
  oldPDFB1B2B3B4Mandatory ≡ false
oldPDFB1B2B3B4MandatoryIsFalse =
  R642.round642OldPDFB1B2B3B4MandatoryIsFalse

oldPDFB7DirectCovarianceEqualityMandatoryIsFalse :
  oldPDFB7DirectCovarianceEqualityMandatory ≡ false
oldPDFB7DirectCovarianceEqualityMandatoryIsFalse =
  R642.round642OldPDFB7DirectCovarianceEqualityMandatoryIsFalse

------------------------------------------------------------------------
-- Legacy publication-readiness anchors.
--
-- These names are intentionally preserved for old manifest/readiness tooling.
-- They expose the historical A6-A9 route only; they do not define the modern
-- canonical proof frontier and they do not promote Clay/global regularity.
------------------------------------------------------------------------

a6TheoremProved : Bool
a6TheoremProved = A6.A6TheoremProved

a7ResidualDepletionProved : Bool
a7ResidualDepletionProved = A7.A7ResidualDepletionGronwallProved

a8FullLocalDefectMonotonicityProved : Bool
a8FullLocalDefectMonotonicityProved = A8.A8FullLocalDefectMonotonicityProved

a9CKNBKMClosureProved : Bool
a9CKNBKMClosureProved = A9.A9CKNBKMClosureProved

nsPaperInterfaceTerminalFalse :
  NSPaperTheoremStatus.clayTerminalPromotion canonicalNSPaperTheoremStatus
  ≡ false
nsPaperInterfaceTerminalFalse =
  NSPaperTheoremStatus.clayTerminalPromotionIsFalse canonicalNSPaperTheoremStatus


periodicClayMaxCutCyclicHelicalVectorTransformClosed : Bool
periodicClayMaxCutCyclicHelicalVectorTransformClosed =
  R650.round650CyclicHelicalVectorTransformClosed

periodicClayMaxCutCyclicHelicalExactCancellationClosed : Bool
periodicClayMaxCutCyclicHelicalExactCancellationClosed =
  R650.round650CyclicHelicalExactCancellationClosed


periodicClayMaxCutOrientedCyclicHelicalCoefficientCancellationClosed : Bool
periodicClayMaxCutOrientedCyclicHelicalCoefficientCancellationClosed =
  R650.round650OrientedCyclicHelicalCoefficientCancellationClosed

periodicClayMaxCutCyclicHelicalPairingNormalFormClosed : Bool
periodicClayMaxCutCyclicHelicalPairingNormalFormClosed =
  R650.round650CyclicHelicalPairingNormalFormClosed

periodicClayMaxCutCyclicHelicalGeometryOrientationClosedOnR700Rows : Bool
periodicClayMaxCutCyclicHelicalGeometryOrientationClosedOnR700Rows =
  R650.round650CyclicHelicalGeometryOrientationClosedOnR700Rows


periodicClayMaxCutActualNestedSpectatorPairingFactorsCoefficient : Bool
periodicClayMaxCutActualNestedSpectatorPairingFactorsCoefficient =
  R650.round650ActualNestedSpectatorPairingFactorsCoefficient

periodicClayMaxCutSelectedSelfInnerThreeOuterLegOrbitClosed : Bool
periodicClayMaxCutSelectedSelfInnerThreeOuterLegOrbitClosed =
  R650.round650SelectedSelfInnerThreeOuterLegOrbitClosed

periodicClayMaxCutGenericExternalInnerThreeOuterLegOrbitClosed : Bool
periodicClayMaxCutGenericExternalInnerThreeOuterLegOrbitClosed =
  R650.round650GenericExternalInnerThreeOuterLegOrbitClosed


periodicClayMaxCutUnitNestedOrbitSelfExternalSplitClosed : Bool
periodicClayMaxCutUnitNestedOrbitSelfExternalSplitClosed =
  R650.round650UnitNestedOrbitSelfExternalSplitClosed

periodicClayMaxCutSelfNestedOrbitExactCancellationClosed : Bool
periodicClayMaxCutSelfNestedOrbitExactCancellationClosed =
  R650.round650SelfNestedOrbitExactCancellationClosed

periodicClayMaxCutExternalNestedOrbitCutoffUniformPaymentClosed : Bool
periodicClayMaxCutExternalNestedOrbitCutoffUniformPaymentClosed =
  R650.round650ExternalNestedOrbitCutoffUniformPaymentClosed

periodicClayMaxCutCompleteSelfOrbitOnSelectedSelfCommutatorCarrier : Bool
periodicClayMaxCutCompleteSelfOrbitOnSelectedSelfCommutatorCarrier =
  R650.round650CompleteSelfOrbitOnSelectedSelfCommutatorCarrier

periodicClayMaxCutCompleteSelfOrbitIsFourSingleSelfCommutatorOrbit : Bool
periodicClayMaxCutCompleteSelfOrbitIsFourSingleSelfCommutatorOrbit =
  R650.round650CompleteSelfOrbitIsFourSingleSelfCommutatorOrbit

periodicClayMaxCutSelfOrbitNaiveRowLocalFibreReindexAvailable : Bool
periodicClayMaxCutSelfOrbitNaiveRowLocalFibreReindexAvailable =
  R650.round650SelfOrbitNaiveRowLocalEnergyLegFibreReindexAvailable

periodicClayMaxCutCompleteSingleSelfOrbitIsThreeGlobalMaskedRows : Bool
periodicClayMaxCutCompleteSingleSelfOrbitIsThreeGlobalMaskedRows =
  R650.round650CompleteSingleSelfOrbitIsThreeGlobalMaskedRows

periodicClayMaxCutRemainingSelfExactQuestionIsGlobalMaskedRowCancellation : Bool
periodicClayMaxCutRemainingSelfExactQuestionIsGlobalMaskedRowCancellation =
  R650.round650RemainingSelfExactQuestionIsGlobalMaskedRowCancellation


periodicClayMaxCutEachOutputDoubleRowCollapsesToOneCoherentPairing : Bool
periodicClayMaxCutEachOutputDoubleRowCollapsesToOneCoherentPairing =
  R650.round650EachOutputDoubleRowCollapsesToOneCoherentPairing

periodicClayMaxCutGlobalMaskedSelfSumRegroupedByLiteralOutputs : Bool
periodicClayMaxCutGlobalMaskedSelfSumRegroupedByLiteralOutputs =
  R650.round650GlobalMaskedSelfSumRegroupedByLiteralOutputs

periodicClayMaxCutMixedOutputFoldRealityClosed : Bool
periodicClayMaxCutMixedOutputFoldRealityClosed =
  R650.round650MixedOutputFoldRealityClosed

periodicClayMaxCutSelectedSelfFoldRealityClosed : Bool
periodicClayMaxCutSelectedSelfFoldRealityClosed =
  R650.round650SelectedSelfFoldRealityClosed

periodicClayMaxCutRealityPairingEvenOnLiteralSelfCarrier : Bool
periodicClayMaxCutRealityPairingEvenOnLiteralSelfCarrier =
  R650.round650RealityPairingEvenOnLiteralSelfCarrier

periodicClayMaxCutRealityCancelsLiteralSelectedSelfPairing : Bool
periodicClayMaxCutRealityCancelsLiteralSelectedSelfPairing =
  R650.round650RealityCancelsLiteralSelectedSelfPairing

periodicClayMaxCutZeroSafeMultiplierCellIsDoubleSelectedSelfCell : Bool
periodicClayMaxCutZeroSafeMultiplierCellIsDoubleSelectedSelfCell =
  R650.round650ZeroSafeMultiplierCellIsDoubleSelectedSelfCell

periodicClayMaxCutSelectedSelfMultiplierFoldHelicitySplitClosed : Bool
periodicClayMaxCutSelectedSelfMultiplierFoldHelicitySplitClosed =
  R650.round650SelectedSelfMultiplierFoldHelicitySplitClosed

periodicClayMaxCutDoubleSelectedSelfWorkIsHomochiralPlusHeterochiral : Bool
periodicClayMaxCutDoubleSelectedSelfWorkIsHomochiralPlusHeterochiral =
  R650.round650DoubleSelectedSelfWorkIsHomochiralPlusHeterochiral

periodicClayMaxCutCompleteSelfOrbitIsTwelveOutputPairings : Bool
periodicClayMaxCutCompleteSelfOrbitIsTwelveOutputPairings =
  R650.round650CompleteSelfOrbitIsTwelveOutputPairings

periodicClayMaxCutSelfExternalRecombineToSingleGlobalCommutator : Bool
periodicClayMaxCutSelfExternalRecombineToSingleGlobalCommutator =
  R650.round650SelfExternalRecombineToSingleGlobalCommutator

periodicClayMaxCutSeparateSelfCancellationRequiredAfterRecombination : Bool
periodicClayMaxCutSeparateSelfCancellationRequiredAfterRecombination =
  R650.round650SeparateSelfCancellationRequiredAfterRecombination

periodicClayMaxCutSeparateExternalPaymentRequiredAfterRecombination : Bool
periodicClayMaxCutSeparateExternalPaymentRequiredAfterRecombination =
  R650.round650SeparateExternalPaymentRequiredAfterRecombination

periodicClayMaxCutRemainingAnalyticObjectIsCombinedGlobalCommutator : Bool
periodicClayMaxCutRemainingAnalyticObjectIsCombinedGlobalCommutator =
  R650.round650RemainingAnalyticObjectIsCombinedGlobalCommutator
