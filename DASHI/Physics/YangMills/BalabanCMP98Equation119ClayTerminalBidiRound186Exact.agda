{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119ClayTerminalBidiRound186Exact where

------------------------------------------------------------------------
-- ROUND186 A1 BIDI: MULTITHREAD FROM BOTH ENDS OF THE YM/CLAY CHAIN
--
-- Forward thread (literal source side):
--
--   selected physical Balaban background
--     -> literal periodic realization
--     -> CMP98 Eq. (119)
--     -> Q'_k.
--
-- Reverse thread (terminal consumer side): the current Clay promotion owner
-- already records the continuum theorem wire as closed while keeping only the
-- physical-Hamiltonian identification / Clay-statement / external-acceptance
-- promotion boundary fail-closed.
--
-- This file does NOT claim Clay Yang-Mills.  It records the BIDI cut induced by
-- simultaneously consuming the strongest current Eq. (119) producer and the
-- strongest current terminal Clay-facing owner.  In particular, older
-- final-state ledgers which still enumerate H3a/H3b/OS as open are diagnostic
-- history; they are not allowed to re-expand the current shortest cut once the
-- canonical terminal theorem-wire owner records those downstream stages as
-- constructed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98Equation119PhysicalSelectedBackgroundRound185Exact as R185
import DASHI.Physics.Closure.YMThermodynamicOSWightmanOperatorBoundaryReceipt as TerminalWire
import DASHI.Physics.Closure.YMClayPromotionBoundary as Clay
import DASHI.Physics.Closure.YMCompletionBoundaryTightening as Completion

------------------------------------------------------------------------
-- Two-ended cut classification.
------------------------------------------------------------------------

data YMClayBidiFrontier : Set where
  literalPhysicalBackgroundRealization : YMClayBidiFrontier
  physicalHamiltonianMassGapIdentification : YMClayBidiFrontier
  clayStatementFormulationEquivalence : YMClayBidiFrontier
  externalAcceptanceOrReview : YMClayBidiFrontier

-- The current terminal wire already owns the continuum reconstruction chain.
terminalThermodynamicLimitConstructed :
  TerminalWire.thermodynamicLimitConstructed
    TerminalWire.canonicalYMThermodynamicOSWightmanOperatorBoundaryReceipt
  ≡ true
terminalThermodynamicLimitConstructed = refl

terminalOSPositivityConstructed :
  TerminalWire.osPositivityConstructed
    TerminalWire.canonicalYMThermodynamicOSWightmanOperatorBoundaryReceipt
  ≡ true
terminalOSPositivityConstructed = refl

terminalWightmanConstructed :
  TerminalWire.wightmanReconstructionConstructed
    TerminalWire.canonicalYMThermodynamicOSWightmanOperatorBoundaryReceipt
  ≡ true
terminalWightmanConstructed = refl

terminalOperatorConvergenceConstructed :
  TerminalWire.operatorConvergenceConstructed
    TerminalWire.canonicalYMThermodynamicOSWightmanOperatorBoundaryReceipt
  ≡ true
terminalOperatorConvergenceConstructed = refl

terminalUniformMassGapConstructed :
  TerminalWire.uniformMassGapConstructed
    TerminalWire.canonicalYMThermodynamicOSWightmanOperatorBoundaryReceipt
  ≡ true
terminalUniformMassGapConstructed = refl

terminalContinuumUniquenessConstructed :
  TerminalWire.continuumUniquenessConstructed
    TerminalWire.canonicalYMThermodynamicOSWightmanOperatorBoundaryReceipt
  ≡ true
terminalContinuumUniquenessConstructed = refl

-- But terminal promotion itself remains fail-closed.
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
-- The forward Eq. (119) side and reverse Clay side now meet at two genuinely
-- different seams.  The local analytic seam is the physical realization from
-- R185; the final promotion seam is the Clay physical-Hamiltonian/statement
-- boundary.  The already-constructed terminal theorem wire is not duplicated
-- here as another chain of receipts.
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
  ; Eq119ToClayTerminalBidiCut.completionBoundary =
      Completion.ymCompletionBoundaryStatus
  ; Eq119ToClayTerminalBidiCut.completionBoundaryIsCanonical = refl
  ; Eq119ToClayTerminalBidiCut.clayBoundary = Clay.clayPromotionBoundary
  ; Eq119ToClayTerminalBidiCut.clayBoundaryIsCanonical = refl
  }

cmp98Equation119ClayTerminalBidiRound186Level : ProofLevel
cmp98Equation119ClayTerminalBidiRound186Level = machineChecked

-- Highest-alpha source-side leaf after BIDI compression:
literalCMP98PhysicalBackgroundRealizationRound186Level : ProofLevel
literalCMP98PhysicalBackgroundRealizationRound186Level =
  R185.literalCMP98PhysicalBackgroundRealizationRound185Level

-- Highest-alpha terminal mathematical leaf after consuming the already-owned
-- theorem wire.  External review/acceptance remains governance, not math.
physicalHamiltonianClayIdentificationRound186Level : ProofLevel
physicalHamiltonianClayIdentificationRound186Level = conditional
