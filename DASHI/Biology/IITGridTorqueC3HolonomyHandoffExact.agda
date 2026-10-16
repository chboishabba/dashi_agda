module DASHI.Biology.IITGridTorqueC3HolonomyHandoffExact where

------------------------------------------------------------------------
-- GRID SOCKET C3 HOLONOMY -> ORIENTED-BRACKET PHASE HANDOFF
--
-- The sibling torque/oriented-bracket work uses the same symbolic C3Phase
-- carrier and the same zeta/zeta^2 conjugation law as the grid socket chart.
-- This module does not import sibling theorem authority across branches.
-- Instead it states the exact proof-relevant interface whose inhabitant turns
-- the grid socket chart into the bracket phase chart, and proves that one-hop
-- and whole-path holonomy then intertwine automatically.
--
-- Once the donor owner is synchronized, its canonical positive/negative bracket
-- voxels can inhabit this interface directly.  Until then the compiler is paid
-- but the concrete donor instance is intentionally left unclaimed.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Algebra.TriadicDepthOneCharacters as C3
import DASHI.Moonshine.C3FourierConjugationExact as Fourier
import DASHI.Biology.IITCausalPantsFibreGluingExact as Pants
import DASHI.Biology.IITXORGridLoopHolonomyExact as Grid

------------------------------------------------------------------------
-- 1. Minimal same-phase interface required from an oriented bracket owner.
------------------------------------------------------------------------

record OrientedBracketPhaseInterface (Bracket : Set) : Set₁ where
  constructor oriented-bracket-phase-interface
  field
    positiveBracket : Bracket
    negativeBracket : Bracket
    swapBracketInputs : Bracket → Bracket
    bracketPhase : Bracket → C3.C3Phase

    positiveBracketPhase : bracketPhase positiveBracket ≡ Fourier.zeta
    negativeBracketPhase : bracketPhase negativeBracket ≡ Fourier.zetaSquared

    swapPositiveToNegative :
      swapBracketInputs positiveBracket ≡ negativeBracket
    swapNegativeToPositive :
      swapBracketInputs negativeBracket ≡ positiveBracket

    swapConjugatesBracketPhase :
      (bracket : Bracket) →
      bracketPhase (swapBracketInputs bracket)
      ≡ Fourier.inversePhase (bracketPhase bracket)
open OrientedBracketPhaseInterface public

------------------------------------------------------------------------
-- 2. The socket chart embeds into any bracket interface satisfying those exact
--    phase receipts.
------------------------------------------------------------------------

portBracket :
  {Bracket : Set} →
  OrientedBracketPhaseInterface Bracket →
  Pants.InputPort → Bracket
portBracket witness Pants.inputA = positiveBracket witness
portBracket witness Pants.inputB = negativeBracket witness

portPhaseIntertwines :
  {Bracket : Set} →
  (witness : OrientedBracketPhaseInterface Bracket) →
  (port : Pants.InputPort) →
  Grid.socketPhase port ≡ bracketPhase witness (portBracket witness port)
portPhaseIntertwines witness Pants.inputA =
  sym (positiveBracketPhase witness)
portPhaseIntertwines witness Pants.inputB =
  sym (negativeBracketPhase witness)

portSwapIntertwines :
  {Bracket : Set} →
  (witness : OrientedBracketPhaseInterface Bracket) →
  (port : Pants.InputPort) →
  swapBracketInputs witness (portBracket witness port)
  ≡ portBracket witness (Grid.swapPort port)
portSwapIntertwines witness Pants.inputA = swapPositiveToNegative witness
portSwapIntertwines witness Pants.inputB = swapNegativeToPositive witness

------------------------------------------------------------------------
-- 3. Whole-path same-object phase compiler.
------------------------------------------------------------------------

bracketPathHolonomy :
  {Bracket : Set} →
  OrientedBracketPhaseInterface Bracket →
  Grid.SocketPath → C3.C3Phase
bracketPathHolonomy witness [] = Fourier.one
bracketPathHolonomy witness (port ∷ rest) =
  C3.multiplyPhase
    (bracketPhase witness (portBracket witness port))
    (bracketPathHolonomy witness rest)

socketPathIntertwinesBracketPath :
  {Bracket : Set} →
  (witness : OrientedBracketPhaseInterface Bracket) →
  (path : Grid.SocketPath) →
  Grid.phaseHolonomy path ≡ bracketPathHolonomy witness path
socketPathIntertwinesBracketPath witness [] = refl
socketPathIntertwinesBracketPath witness (port ∷ rest)
  rewrite portPhaseIntertwines witness port
        | socketPathIntertwinesBracketPath witness rest = refl

bracketPathSwapConjugates :
  {Bracket : Set} →
  (witness : OrientedBracketPhaseInterface Bracket) →
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
-- 4. Source receipt for the sibling donor.  This is attribution/status, not an
--    imported proof.  PR #1164's OrientedThreeAxisBracket369Exact delegates to
--    TorqueTrialectic369Exact and source-writes the required same C3 carrier,
--    positive/negative phase sectors, input reversal, and phase conjugation.
------------------------------------------------------------------------

record TorqueBracketDonorSourceReceipt : Set where
  constructor torque-bracket-donor-source-receipt
  field
    siblingPR : Nat
    observedHead : String
    ownerPath : String
    sameC3PhaseCarrierSourceWritten : Bool
    positiveBracketMapsToZetaSourceWritten : Bool
    negativeBracketMapsToZetaSquaredSourceWritten : Bool
    inputSwapExchangesOrientationsSourceWritten : Bool
    inputSwapConjugatesPhaseSourceWritten : Bool
    donorTheoremAuthorityImportedOnThisBranch : Bool
open TorqueBracketDonorSourceReceipt public

canonicalTorqueBracketDonorSourceReceipt : TorqueBracketDonorSourceReceipt
canonicalTorqueBracketDonorSourceReceipt =
  torque-bracket-donor-source-receipt
    1164
    "f8318e1a80e076a42ba54d67a8a9d5efae325dbe"
    "DASHI/Physics/Foundations/OrientedThreeAxisBracket369Exact.agda"
    true true true true true false

record GridTorqueHolonomyHandoffBoundary : Set where
  constructor grid-torque-holonomy-handoff-boundary
  field
    proofRelevantSamePhaseCompilerPaid : Bool
    oneHopSocketBracketPhaseIntertwinerCompiled : Bool
    wholePathHolonomyIntertwinerCompiled : Bool
    swapConjugationTransportCompiled : Bool
    siblingSourceSatisfiesRequiredShape : Bool
    concreteSiblingInterfaceInhabitantImportedHere : Bool
    phaseIntertwinerIdentifiesPhysicalAmplitude : Bool
    phaseIntertwinerIdentifiesAllPhysicalMechanisms : Bool
open GridTorqueHolonomyHandoffBoundary public

canonicalGridTorqueHolonomyHandoffBoundary : GridTorqueHolonomyHandoffBoundary
canonicalGridTorqueHolonomyHandoffBoundary =
  grid-torque-holonomy-handoff-boundary
    true true true true true false false false
