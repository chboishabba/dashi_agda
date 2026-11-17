module DASHI.Papers.YangMills.TheoremInterface where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.SelfAdjointYangMillsHamiltonianOnCarrierQuotient
  as SelfAdjointYM
import DASHI.Physics.Closure.YMBochnerWeitzenbockHamiltonianDominationBoundary
  as Bochner
import DASHI.Physics.Closure.YMHamiltonianDominationCompositeBoundary
  as Domination
import DASHI.Physics.Closure.Gate3PAWOTGUniformSeparationTargetReceipt
  as PAWOTG
import DASHI.Physics.Closure.YMFinalStateReceipt as Final

------------------------------------------------------------------------
-- Paper-facing Yang-Mills theorem interface.
--
-- This module only re-exposes existing closure receipts.  It records which
-- theorem surfaces are currently usable by a paper draft and keeps the Clay
-- terminal promotion fail-closed.

data YangMillsPaperStatus : Set where
  importedReceiptsAssembled_clayTerminalFalse :
    YangMillsPaperStatus

record YangMillsPaperTheoremInterface : Setω where
  field
    status :
      YangMillsPaperStatus

    statusIsCanonical :
      status ≡ importedReceiptsAssembled_clayTerminalFalse

    selfAdjointGapBridgeReceipt :
      SelfAdjointYM.Gate8Term4StoneYMHamiltonianGapBridgeReceipt

    selfAdjointSelectedLowerBoundConcrete :
      SelfAdjointYM.selectedCarrierLowerBoundConcrete
        selfAdjointGapBridgeReceipt
      ≡
      true

    selfAdjointSelectedLowerBoundNotTransported :
      SelfAdjointYM.selectedLowerBoundTransportedToPhysicalYM
        selfAdjointGapBridgeReceipt
      ≡
      false

    selfAdjointPhysicalGapStillFalse :
      SelfAdjointYM.physicalStoneYMSpectralGapPromoted
        selfAdjointGapBridgeReceipt
      ≡
      false

    selfAdjointContinuumClayStillFalse :
      SelfAdjointYM.continuumClayMassGapPromoted
        selfAdjointGapBridgeReceipt
      ≡
      false

    bochnerWeitzenbockDominationReceipt :
      Bochner.YMBochnerWeitzenbockHamiltonianDominationBoundary

    bochnerWeitzenbockIdentityProved :
      Bochner.bochnerWeitzenbockIdentityProved ≡ true

    deltaYMCoercivityProved :
      Bochner.deltaYMCoercivityProved ≡ true

    holonomyPositiveActionProved :
      Bochner.holonomyPositiveActionProved ≡ true

    localHamiltonianDominationProved :
      Bochner.hamiltonianDominationProved ≡ true

    localSpectralMarginProved :
      Bochner.spectralMarginProved ≡ true

    localOSTransferStillFalse :
      Bochner.osTransferProved ≡ false

    localContinuumNoSpectralPollutionStillFalse :
      Bochner.continuumNoSpectralPollutionProved ≡ false

    localYMClayStillFalse :
      Bochner.ymClayPromoted ≡ false

    localTerminalStillFalse :
      Bochner.terminalPromotion ≡ false

    conservativeDominationCompositeReceipt :
      Domination.YMHamiltonianDominationCompositeBoundary

    conservativeCompositeDominationStillFalse :
      Domination.dominationTheoremField conservativeDominationCompositeReceipt
      ≡
      false

    conservativeCompositeOSTransferStillFalse :
      Domination.osTransferTheoremField conservativeDominationCompositeReceipt
      ≡
      false

    conservativeCompositeContinuumNoPollutionStillFalse :
      Domination.continuumNoSpectralPollutionTheoremField
        conservativeDominationCompositeReceipt
      ≡
      false

    conservativeCompositeClayStillFalse :
      Domination.ymClayTheoremField conservativeDominationCompositeReceipt
      ≡
      false

    gate3PAWOTGTransferReceipt :
      PAWOTG.Gate3PAWOTGUniformSeparationTargetReceipt

    pawotgInfANPositive :
      PAWOTG.infANPositiveProvedHere gate3PAWOTGTransferReceipt ≡ true

    pawotgMoscoTransfer :
      PAWOTG.moscoTransferProvedHere gate3PAWOTGTransferReceipt ≡ true

    pawotgNoSpectralPollutionTransfer :
      PAWOTG.noSpectralPollutionTransferProvedHere
        gate3PAWOTGTransferReceipt
      ≡
      true

    pawotgMassShellRouteConditional :
      PAWOTG.massShellRouteAvailableConditionally
        gate3PAWOTGTransferReceipt
      ≡
      true

    pawotgGate3StillFalse :
      PAWOTG.gate3Promoted gate3PAWOTGTransferReceipt ≡ false

    pawotgClayStillFalse :
      PAWOTG.clayPromoted gate3PAWOTGTransferReceipt ≡ false

    finalStateReceipt :
      Final.YMFinalStateReceipt

    finalContinuumYMConstructed :
      Final.continuumYangMillsConstructed finalStateReceipt ≡ true

    finalUniformMassGapConstructed :
      Final.uniformMassGapConstructed finalStateReceipt ≡ true

    finalContinuumUniquenessConstructed :
      Final.continuumUniquenessConstructed finalStateReceipt ≡ true

    finalClayStillFalse :
      Final.clayYangMillsPromoted finalStateReceipt ≡ false

    paperClayTerminalPromoted :
      Bool

    paperClayTerminalPromotedIsFalse :
      paperClayTerminalPromoted ≡ false

    exactSummary :
      List String

open YangMillsPaperTheoremInterface public

canonicalYangMillsPaperTheoremInterface :
  YangMillsPaperTheoremInterface
canonicalYangMillsPaperTheoremInterface =
  record
    { status =
        importedReceiptsAssembled_clayTerminalFalse
    ; statusIsCanonical =
        refl
    ; selfAdjointGapBridgeReceipt =
        SelfAdjointYM.canonicalGate8Term4StoneYMHamiltonianGapBridgeReceipt
    ; selfAdjointSelectedLowerBoundConcrete =
        SelfAdjointYM.selectedCarrierLowerBoundConcreteIsTrue
          SelfAdjointYM.canonicalGate8Term4StoneYMHamiltonianGapBridgeReceipt
    ; selfAdjointSelectedLowerBoundNotTransported =
        SelfAdjointYM.selectedLowerBoundTransportedToPhysicalYMIsFalse
          SelfAdjointYM.canonicalGate8Term4StoneYMHamiltonianGapBridgeReceipt
    ; selfAdjointPhysicalGapStillFalse =
        SelfAdjointYM.physicalStoneYMSpectralGapPromotedIsFalse
          SelfAdjointYM.canonicalGate8Term4StoneYMHamiltonianGapBridgeReceipt
    ; selfAdjointContinuumClayStillFalse =
        SelfAdjointYM.continuumClayMassGapPromotedIsFalse
          SelfAdjointYM.canonicalGate8Term4StoneYMHamiltonianGapBridgeReceipt
    ; bochnerWeitzenbockDominationReceipt =
        Bochner.canonicalYMBochnerWeitzenbockHamiltonianDominationBoundary
    ; bochnerWeitzenbockIdentityProved =
        Bochner.bochnerWeitzenbockIdentityProvedIsTrue
    ; deltaYMCoercivityProved =
        Bochner.deltaYMCoercivityProvedIsTrue
    ; holonomyPositiveActionProved =
        Bochner.holonomyPositiveActionProvedIsTrue
    ; localHamiltonianDominationProved =
        Bochner.hamiltonianDominationProvedIsTrue
    ; localSpectralMarginProved =
        Bochner.spectralMarginProvedIsTrue
    ; localOSTransferStillFalse =
        Bochner.osTransferProvedIsFalse
    ; localContinuumNoSpectralPollutionStillFalse =
        Bochner.continuumNoSpectralPollutionProvedIsFalse
    ; localYMClayStillFalse =
        Bochner.ymClayPromotedIsFalse
    ; localTerminalStillFalse =
        Bochner.terminalPromotionIsFalse
    ; conservativeDominationCompositeReceipt =
        Domination.canonicalYMHamiltonianDominationCompositeBoundary
    ; conservativeCompositeDominationStillFalse =
        Domination.canonicalCompositeDominationFalse
    ; conservativeCompositeOSTransferStillFalse =
        Domination.canonicalCompositeOSTransferFalse
    ; conservativeCompositeContinuumNoPollutionStillFalse =
        Domination.canonicalCompositeContinuumNoSpectralPollutionFalse
    ; conservativeCompositeClayStillFalse =
        Domination.canonicalCompositeYMClayFalse
    ; gate3PAWOTGTransferReceipt =
        PAWOTG.canonicalGate3PAWOTGUniformSeparationTargetReceipt
    ; pawotgInfANPositive =
        PAWOTG.gate3PAWOTGUniformSeparationTargetInfAPositive
    ; pawotgMoscoTransfer =
        PAWOTG.gate3PAWOTGUniformSeparationTargetMoscoTransfer
    ; pawotgNoSpectralPollutionTransfer =
        PAWOTG.gate3PAWOTGUniformSeparationTargetNoSpectralPollutionTransfer
    ; pawotgMassShellRouteConditional =
        PAWOTG.gate3PAWOTGUniformSeparationTargetRecordsConditionalMassShellRoute
    ; pawotgGate3StillFalse =
        PAWOTG.gate3PAWOTGUniformSeparationTargetNoGate3Promotion
    ; pawotgClayStillFalse =
        PAWOTG.gate3PAWOTGUniformSeparationTargetNoClayPromotion
    ; finalStateReceipt =
        Final.canonicalYMFinalStateReceipt
    ; finalContinuumYMConstructed =
        refl
    ; finalUniformMassGapConstructed =
        refl
    ; finalContinuumUniquenessConstructed =
        refl
    ; finalClayStillFalse =
        Final.ymFinalStateKeepsClayFalse
    ; paperClayTerminalPromoted =
        false
    ; paperClayTerminalPromotedIsFalse =
        refl
    ; exactSummary =
        "self-adjoint selected-carrier lower bound recorded, not transported to physical YM"
        ∷ "local finite Bochner-Weitzenbock identity, Delta_YM coercivity, holonomy positivity, domination, and spectral margin are recorded true"
        ∷ "older conservative domination composite remains fail-closed for OS/continuum/Clay consumers"
        ∷ "Gate3 PAWOTG transfer payload is recorded while Gate3 and Clay stay false"
        ∷ "YM final-state receipt is imported and terminal Clay promotion remains false"
        ∷ []
    }

paperInterfaceSelfAdjointPhysicalGapFalse :
  selfAdjointPhysicalGapStillFalse
    canonicalYangMillsPaperTheoremInterface
  ≡
  refl
paperInterfaceSelfAdjointPhysicalGapFalse =
  refl

paperInterfaceDominationFalse :
  Domination.dominationTheoremField
    (conservativeDominationCompositeReceipt
      canonicalYangMillsPaperTheoremInterface)
  ≡
  false
paperInterfaceDominationFalse =
  refl

paperInterfaceLocalDominationTrue :
  Bochner.hamiltonianDominationProved ≡ true
paperInterfaceLocalDominationTrue =
  Bochner.hamiltonianDominationProvedIsTrue

paperInterfaceLocalSpectralMarginTrue :
  Bochner.spectralMarginProved ≡ true
paperInterfaceLocalSpectralMarginTrue =
  Bochner.spectralMarginProvedIsTrue

paperInterfacePAWOTGTransferTrue :
  PAWOTG.noSpectralPollutionTransferProvedHere
    (gate3PAWOTGTransferReceipt canonicalYangMillsPaperTheoremInterface)
  ≡
  true
paperInterfacePAWOTGTransferTrue =
  refl

paperInterfaceFinalClayFalse :
  Final.clayYangMillsPromoted
    (finalStateReceipt canonicalYangMillsPaperTheoremInterface)
  ≡
  false
paperInterfaceFinalClayFalse =
  refl

paperInterfaceClayTerminalFalse :
  paperClayTerminalPromoted canonicalYangMillsPaperTheoremInterface
  ≡
  false
paperInterfaceClayTerminalFalse =
  refl
