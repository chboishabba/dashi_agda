{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119ClayTerminalBidiRound186Exact where

------------------------------------------------------------------------
-- ROUND186 A1 BIDI: CORRECTED TWO-ENDED YM/CLAY CUT
--
-- Forward/source side:
--   selected physical Balaban background
--     -> literal periodic realization
--     -> CMP98 Eq. (119)
--     -> Q'_k.
--
-- Reverse/terminal side correction:
-- `YMThermodynamicOSWightmanOperatorBoundaryReceipt` explicitly says it is a
-- fail-closed dependency/receipt surface and does NOT prove thermodynamic
-- limit, OS positivity, Wightman reconstruction, operator convergence,
-- uniform mass gap, or continuum uniqueness.  Its legacy `*Constructed=true`
-- fields therefore record historical wire state only.  They are not theorem
-- proofs and must not collapse M8/M9 or the physical continuum frontier.
--
-- The authoritative current theorem-strength status is owned by
-- `YMOperatorDomainContinuumFrontier2026Exact`; this module consumes it rather
-- than letting legacy receipt bits outrank the actual proof objects.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98Equation119PhysicalSelectedBackgroundRound185Exact as R185
import DASHI.Physics.YangMills.YMOperatorDomainContinuumFrontier2026Exact as Frontier
import DASHI.Physics.Closure.YMThermodynamicOSWightmanOperatorBoundaryReceipt as TerminalWire
import DASHI.Physics.Closure.YMClayPromotionBoundary as Clay
import DASHI.Physics.Closure.YMCompletionBoundaryTightening as Completion

------------------------------------------------------------------------
-- Two-ended cut classification.
------------------------------------------------------------------------

data YMClayBidiFrontier : Set where
  literalPhysicalBackgroundRealization : YMClayBidiFrontier
  physicalActionVariationHamiltonianSameObject : YMClayBidiFrontier
  physicalHamiltonianDomainAndSelfAdjointness : YMClayBidiFrontier
  constructiveOSDynamicsAndYMIdentification : YMClayBidiFrontier
  physicalVacuumRecoveryOrDenseCoreProducer : YMClayBidiFrontier
  finiteToContinuumPhysicalIdentification : YMClayBidiFrontier
  clayStatementFormulationEquivalence : YMClayBidiFrontier
  externalAcceptanceOrReview : YMClayBidiFrontier

------------------------------------------------------------------------
-- Legacy receipt bits are preserved as historical facts about the receipt,
-- but explicitly bounded away from theorem-strength interpretation.
------------------------------------------------------------------------

legacyTerminalThermodynamicReceiptBitIsTrue :
  TerminalWire.thermodynamicLimitConstructed
    TerminalWire.canonicalYMThermodynamicOSWightmanOperatorBoundaryReceipt
  ≡ true
legacyTerminalThermodynamicReceiptBitIsTrue = refl

legacyTerminalOSPositivityReceiptBitIsTrue :
  TerminalWire.osPositivityConstructed
    TerminalWire.canonicalYMThermodynamicOSWightmanOperatorBoundaryReceipt
  ≡ true
legacyTerminalOSPositivityReceiptBitIsTrue = refl

legacyTerminalWightmanReceiptBitIsTrue :
  TerminalWire.wightmanReconstructionConstructed
    TerminalWire.canonicalYMThermodynamicOSWightmanOperatorBoundaryReceipt
  ≡ true
legacyTerminalWightmanReceiptBitIsTrue = refl

legacyTerminalOperatorConvergenceReceiptBitIsTrue :
  TerminalWire.operatorConvergenceConstructed
    TerminalWire.canonicalYMThermodynamicOSWightmanOperatorBoundaryReceipt
  ≡ true
legacyTerminalOperatorConvergenceReceiptBitIsTrue = refl

------------------------------------------------------------------------
-- Current theorem-strength frontier.  These false equalities outrank the
-- legacy receipt bits for promotion/dependency purposes.
------------------------------------------------------------------------

constructiveContinuumOSWightmanStillOpen :
  Frontier.continuumOSWightmanPackageClosed
    Frontier.canonicalYMOperatorContinuumFrontier
  ≡ false
constructiveContinuumOSWightmanStillOpen = refl

constructiveYMEqualsOSEvolutionStillOpen :
  Frontier.ymEvolutionEqualsOSReconstructedEvolutionClosed
    Frontier.canonicalYMOperatorContinuumFrontier
  ≡ false
constructiveYMEqualsOSEvolutionStillOpen = refl

physicalVacuumRecoverySystemStillOpen :
  Frontier.physicalVacuumRecoverySystemConstructed
    Frontier.canonicalYMOperatorContinuumFrontier
  ≡ false
physicalVacuumRecoverySystemStillOpen = refl

physicalClosedFormIdentificationStillOpen :
  Frontier.physicalClosedFormOrResolventIdentificationClosed
    Frontier.canonicalYMOperatorContinuumFrontier
  ≡ false
physicalClosedFormIdentificationStillOpen = refl

finiteToContinuumPhysicalConstructionStillOpen :
  Frontier.finiteToContinuumYMConstructionClosed
    Frontier.canonicalYMOperatorContinuumFrontier
  ≡ false
finiteToContinuumPhysicalConstructionStillOpen = refl

physicalHamiltonianDomainStillOpen :
  Frontier.genuinePartialDomainHamiltonianFormalized
    Frontier.canonicalYMOperatorContinuumFrontier
  ≡ false
physicalHamiltonianDomainStillOpen = refl

physicalSelfAdjointSelectedYMFormStillOpen :
  Frontier.physicalSelfAdjointSelectedYMFormClosed
    Frontier.canonicalYMOperatorContinuumFrontier
  ≡ false
physicalSelfAdjointSelectedYMFormStillOpen = refl

-- Terminal promotion itself remains fail-closed.
terminalClayPromotionStillFalse :
  Clay.clayYangMillsPromoted ≡ false
terminalClayPromotionStillFalse = refl

terminalProvidersStillNotAllInternal :
  Clay.allProvidersDerivedInRepo ≡ false
terminalProvidersStillNotAllInternal = refl

terminalStatementBoundaryStillOpen :
  Clay.clayStatementBoundaryDischarged ≡ false
terminalStatementBoundaryStillOpen = refl

------------------------------------------------------------------------
-- Corrected BIDI cut owner.
------------------------------------------------------------------------

record Eq119ToClayTerminalBidiCut : Set where
  field
    eq119PhysicalBackgroundSide : ProofLevel
    eq119PhysicalBackgroundSideIsCurrent :
      eq119PhysicalBackgroundSide
        ≡ R185.cmp98Equation119PhysicalSelectedBackgroundRound185Level

    terminalWire :
      TerminalWire.YMThermodynamicOSWightmanOperatorBoundaryReceipt

    terminalWireIsCanonical :
      terminalWire
        ≡ TerminalWire.canonicalYMThermodynamicOSWightmanOperatorBoundaryReceipt

    terminalWireIsReceiptNotAnalyticClosure :
      Frontier.wightmanQueueConstructiveDynamicsKernelClosed ≡ false

    completionBoundary :
      Completion.YMCompletionBoundaryStatus

    completionBoundaryIsCanonical :
      completionBoundary ≡ Completion.ymCompletionBoundaryStatus

    clayBoundary :
      Clay.ClayPromotionBoundary

    clayBoundaryIsCanonical :
      clayBoundary ≡ Clay.clayPromotionBoundary

canonicalEq119ToClayTerminalBidiCut : Eq119ToClayTerminalBidiCut
canonicalEq119ToClayTerminalBidiCut = record
  { Eq119ToClayTerminalBidiCut.eq119PhysicalBackgroundSide =
      R185.cmp98Equation119PhysicalSelectedBackgroundRound185Level
  ; Eq119ToClayTerminalBidiCut.eq119PhysicalBackgroundSideIsCurrent = refl
  ; Eq119ToClayTerminalBidiCut.terminalWire =
      TerminalWire.canonicalYMThermodynamicOSWightmanOperatorBoundaryReceipt
  ; Eq119ToClayTerminalBidiCut.terminalWireIsCanonical = refl
  ; Eq119ToClayTerminalBidiCut.terminalWireIsReceiptNotAnalyticClosure = refl
  ; Eq119ToClayTerminalBidiCut.completionBoundary =
      Completion.ymCompletionBoundaryStatus
  ; Eq119ToClayTerminalBidiCut.completionBoundaryIsCanonical = refl
  ; Eq119ToClayTerminalBidiCut.clayBoundary = Clay.clayPromotionBoundary
  ; Eq119ToClayTerminalBidiCut.clayBoundaryIsCanonical = refl
  }

cmp98Equation119ClayTerminalBidiRound186Level : ProofLevel
cmp98Equation119ClayTerminalBidiRound186Level = machineChecked

-- Highest-alpha source-side leaf after corrected BIDI compression.
literalCMP98PhysicalBackgroundRealizationRound186Level : ProofLevel
literalCMP98PhysicalBackgroundRealizationRound186Level =
  R185.literalCMP98PhysicalBackgroundRealizationRound185Level

-- The terminal mathematical leaf is not merely Clay statement wording: M7/M8/
-- M9 and the physical continuum identification remain actual mathematical
-- producers.  External review/acceptance remains governance after those close.
physicalHamiltonianClayIdentificationRound186Level : ProofLevel
physicalHamiltonianClayIdentificationRound186Level = conditional
