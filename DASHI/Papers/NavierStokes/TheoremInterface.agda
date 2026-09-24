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
