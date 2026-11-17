module DASHI.Biology.IITGridTorqueC3HolonomyHandoffExact where

------------------------------------------------------------------------
-- GRID SOCKET C3 HOLONOMY -> ORIENTED-BRACKET PHASE HANDOFF
--
-- The synchronized torque/oriented-bracket owner uses the same symbolic
-- C3Phase carrier and the same zeta/zeta^2 conjugation law as the grid socket
-- chart.  The proof-relevant interface below first isolates the exact payment,
-- then the canonical xyz/xzy donor voxels inhabit it on this branch.
--
-- This is a same-object finite PHASE weld only.  It does not identify torque
-- magnitude, continuous amplitudes, or physical mechanisms with IIT/XOR.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Algebra.TriadicDepthOneCharacters as C3
import DASHI.Moonshine.C3FourierConjugationExact as Fourier
import DASHI.Biology.IITCausalPantsFibreGluingExact as Pants
import DASHI.Biology.IITXORGridLoopHolonomyExact as Grid
import DASHI.Physics.Foundations.OrientedThreeAxisBracket369Exact as Bracket

------------------------------------------------------------------------
-- 1. Minimal same-phase interface required from an oriented bracket owner.
------------------------------------------------------------------------

record OrientedBracketPhaseInterface (BracketCarrier : Set) : Set₁ where
  constructor oriented-bracket-phase-interface
  field
    positiveBracket : BracketCarrier
    negativeBracket : BracketCarrier
    swapBracketInputs : BracketCarrier → BracketCarrier
    bracketPhase : BracketCarrier → C3.C3Phase

    positiveBracketPhase : bracketPhase positiveBracket ≡ Fourier.zeta
    negativeBracketPhase : bracketPhase negativeBracket ≡ Fourier.zetaSquared

    swapPositiveToNegative :
      swapBracketInputs positiveBracket ≡ negativeBracket
    swapNegativeToPositive :
      swapBracketInputs negativeBracket ≡ positiveBracket

    swapConjugatesBracketPhase :
      (bracket : BracketCarrier) →
      bracketPhase (swapBracketInputs bracket)
      ≡ Fourier.inversePhase (bracketPhase bracket)
open OrientedBracketPhaseInterface public

------------------------------------------------------------------------
-- 2. The socket chart embeds into any bracket interface satisfying those exact
--    phase receipts.
------------------------------------------------------------------------

portBracket :
  {BracketCarrier : Set} →
  OrientedBracketPhaseInterface BracketCarrier →
  Pants.InputPort → BracketCarrier
portBracket witness Pants.inputA = positiveBracket witness
portBracket witness Pants.inputB = negativeBracket witness

portPhaseIntertwines :
  {BracketCarrier : Set} →
  (witness : OrientedBracketPhaseInterface BracketCarrier) →
  (port : Pants.InputPort) →
  Grid.socketPhase port ≡ bracketPhase witness (portBracket witness port)
portPhaseIntertwines witness Pants.inputA =
  sym (positiveBracketPhase witness)
portPhaseIntertwines witness Pants.inputB =
  sym (negativeBracketPhase witness)

portSwapIntertwines :
  {BracketCarrier : Set} →
  (witness : OrientedBracketPhaseInterface BracketCarrier) →
  (port : Pants.InputPort) →
  swapBracketInputs witness (portBracket witness port)
  ≡ portBracket witness (Grid.swapPort port)
portSwapIntertwines witness Pants.inputA = swapPositiveToNegative witness
portSwapIntertwines witness Pants.inputB = swapNegativeToPositive witness

------------------------------------------------------------------------
-- 3. Whole-path same-object phase compiler.
------------------------------------------------------------------------

bracketPathHolonomy :
  {BracketCarrier : Set} →
  OrientedBracketPhaseInterface BracketCarrier →
  Grid.SocketPath → C3.C3Phase
bracketPathHolonomy witness [] = Fourier.one
bracketPathHolonomy witness (port ∷ rest) =
  C3.multiplyPhase
    (bracketPhase witness (portBracket witness port))
    (bracketPathHolonomy witness rest)

socketPathIntertwinesBracketPath :
  {BracketCarrier : Set} →
  (witness : OrientedBracketPhaseInterface BracketCarrier) →
  (path : Grid.SocketPath) →
  Grid.phaseHolonomy path ≡ bracketPathHolonomy witness path
socketPathIntertwinesBracketPath witness [] = refl
socketPathIntertwinesBracketPath witness (port ∷ rest)
  rewrite portPhaseIntertwines witness port
        | socketPathIntertwinesBracketPath witness rest = refl

bracketPathSwapConjugates :
  {BracketCarrier : Set} →
  (witness : OrientedBracketPhaseInterface BracketCarrier) →
  (path : Grid.SocketPath) →
  bracketPathHolonomy witness (Grid.swapSocketPath path)
  ≡ Fourier.inversePhase (bracketPathHolonomy witness path)
bracketPathSwapConjugates witness path =
  trans
    (sym (socketPathIntertwinesBracketPath witness (Grid.swapSocketPath path)))
    (trans
      (Grid.swapPathConjugatesHolonomy path)
      (cong Fourier.inversePhase (socketPathIntertwinesBracketPath witness path)))

------------------------------------------------------------------------
-- 4. Concrete donor instance: A is the positive xyz bracket and B its reversed
--    xzy bracket.  The donor's exact finite phase law now inhabits the compiler.
------------------------------------------------------------------------

actualTorqueBracketPhaseInterface :
  OrientedBracketPhaseInterface Bracket.BracketVoxel
actualTorqueBracketPhaseInterface = oriented-bracket-phase-interface
  Bracket.xyzBracket
  Bracket.xzyBracket
  Bracket.swapBracketInputs
  Bracket.bracketPhase
  refl
  refl
  refl
  refl
  Bracket.swapBracketInputsConjugatesPhase

actualPortPhaseIntertwiner :
  (port : Pants.InputPort) →
  Grid.socketPhase port
  ≡ Bracket.bracketPhase (portBracket actualTorqueBracketPhaseInterface port)
actualPortPhaseIntertwiner =
  portPhaseIntertwines actualTorqueBracketPhaseInterface

actualPathHolonomyIntertwiner :
  (path : Grid.SocketPath) →
  Grid.phaseHolonomy path
  ≡ bracketPathHolonomy actualTorqueBracketPhaseInterface path
actualPathHolonomyIntertwiner =
  socketPathIntertwinesBracketPath actualTorqueBracketPhaseInterface

actualBracketPathSwapConjugates :
  (path : Grid.SocketPath) →
  bracketPathHolonomy actualTorqueBracketPhaseInterface (Grid.swapSocketPath path)
  ≡ Fourier.inversePhase
      (bracketPathHolonomy actualTorqueBracketPhaseInterface path)
actualBracketPathSwapConjugates =
  bracketPathSwapConjugates actualTorqueBracketPhaseInterface

------------------------------------------------------------------------
-- 5. Donor synchronization receipt.  This tracks source provenance separately
--    from kernel status; the current runtime still has no Agda executable.
------------------------------------------------------------------------

record TorqueBracketDonorSourceReceipt : Set where
  constructor torque-bracket-donor-source-receipt
  field
    siblingPR : Nat
    observedDonorHead : String
    ownerPath : String
    sameC3PhaseCarrierSourceWritten : Bool
    positiveBracketMapsToZetaSourceWritten : Bool
    negativeBracketMapsToZetaSquaredSourceWritten : Bool
    inputSwapExchangesOrientationsSourceWritten : Bool
    inputSwapConjugatesPhaseSourceWritten : Bool
    donorSourceOwnerSynchronizedOnThisBranch : Bool
    freshAgdaKernelReceiptPresent : Bool
open TorqueBracketDonorSourceReceipt public

canonicalTorqueBracketDonorSourceReceipt : TorqueBracketDonorSourceReceipt
canonicalTorqueBracketDonorSourceReceipt =
  torque-bracket-donor-source-receipt
    1164
    "f8318e1a80e076a42ba54d67a8a9d5efae325dbe"
    "DASHI/Physics/Foundations/OrientedThreeAxisBracket369Exact.agda"
    true true true true true true false

record GridTorqueHolonomyHandoffBoundary : Set where
  constructor grid-torque-holonomy-handoff-boundary
  field
    proofRelevantSamePhaseCompilerPaid : Bool
    oneHopSocketBracketPhaseIntertwinerSourceWritten : Bool
    wholePathHolonomyIntertwinerSourceWritten : Bool
    swapConjugationTransportSourceWritten : Bool
    concreteTorqueBracketInterfaceInhabitantSourceWritten : Bool
    phaseIntertwinerIdentifiesPhysicalAmplitude : Bool
    phaseIntertwinerIdentifiesAllPhysicalMechanisms : Bool
open GridTorqueHolonomyHandoffBoundary public

canonicalGridTorqueHolonomyHandoffBoundary : GridTorqueHolonomyHandoffBoundary
canonicalGridTorqueHolonomyHandoffBoundary =
  grid-torque-holonomy-handoff-boundary
    true true true true true false false
