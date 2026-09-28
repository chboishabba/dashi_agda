module DASHI.Reasoning.Trialectic369OutgoingFrickeModeBlock18Exact where

------------------------------------------------------------------------
-- FRICKE-STABLE MODE BLOCK: 2 x SHEET9 = 18
--
-- DASHI CONTRIBUTION
--
-- If a distinguished actual multiplicity/inertia element projects on Fine10
-- as the finite Fricke complement, then a single Fine10 x Sheet9 fibre cannot
-- be invariant.  However finite Fricke preserves ComplementMode5 and flips only
-- the binary direct/counter phase.
--
-- Therefore the natural Fricke-stable replacement over one mode is:
--
--   BinaryPhase x Codec.Sheet9
--
-- with 2 * 9 = 18 states.
--
-- This module constructs that block and compiles the action of any supplied
-- FineFrickeInertiaElement on it.  It does not claim that an actual Monster
-- inertia element satisfying that contract has been recognized.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Nonary
import DASHI.Foundations.Base369PointedAppraisalFibreExact as Pointed
import DASHI.Moonshine.Base369Monster3BMultiplicityCompletedTenTritSquareCompilerExact as Compiler
import DASHI.Reasoning.Trialectic369OutgoingSheet9MultiplicityRecognitionExact as Outgoing
import DASHI.Reasoning.Trialectic369OutgoingFineFrickeInvariantNoGoExact as NoGo

------------------------------------------------------------------------
-- 1. One mode-fixed 18-state block.
------------------------------------------------------------------------

ModeBlock18 : Set
ModeBlock18 =
  Nonary.BinaryPhase × Codec.Sheet9

modeBlockStateCount : Nat
modeBlockStateCount = 2 * 9

modeBlockStateCountIsEighteen :
  modeBlockStateCount ≡ 18
modeBlockStateCountIsEighteen = refl

fineAtModePhase :
  Nonary.ComplementMode5 ->
  Nonary.BinaryPhase ->
  Pointed.Fine10
fineAtModePhase mode phase =
  NoGo.decimalToFine10
    (Nonary.decodeModePhase (mode , phase))

embedModeBlock :
  Nonary.ComplementMode5 ->
  ModeBlock18 ->
  Outgoing.TenByNineSurface
embedModeBlock mode (phase , sheet) =
  Outgoing.embedSecondaryAt
    (fineAtModePhase mode phase)
    sheet

------------------------------------------------------------------------
-- 2. Finite Fricke flips phase while preserving the mode.
------------------------------------------------------------------------

modeBlockFricke :
  ModeBlock18 ->
  ModeBlock18
modeBlockFricke (phase , sheet) =
  Nonary.flipBinaryPhase phase , sheet

modeBlockFrickeInvolutive :
  (state : ModeBlock18) ->
  modeBlockFricke (modeBlockFricke state) ≡ state
modeBlockFrickeInvolutive (phase , sheet)
  rewrite Nonary.flipBinaryPhaseInvolutive phase = refl

fineFrickeAtModePhase :
  (mode : Nonary.ComplementMode5) ->
  (phase : Nonary.BinaryPhase) ->
  NoGo.fine10FiniteFricke
    (fineAtModePhase mode phase)
  ≡ fineAtModePhase mode (Nonary.flipBinaryPhase phase)
fineFrickeAtModePhase Nonary.mode09 Nonary.directPhase = refl
fineFrickeAtModePhase Nonary.mode09 Nonary.counterPhase = refl
fineFrickeAtModePhase Nonary.mode18 Nonary.directPhase = refl
fineFrickeAtModePhase Nonary.mode18 Nonary.counterPhase = refl
fineFrickeAtModePhase Nonary.mode27 Nonary.directPhase = refl
fineFrickeAtModePhase Nonary.mode27 Nonary.counterPhase = refl
fineFrickeAtModePhase Nonary.mode36 Nonary.directPhase = refl
fineFrickeAtModePhase Nonary.mode36 Nonary.counterPhase = refl
fineFrickeAtModePhase Nonary.mode45 Nonary.directPhase = refl
fineFrickeAtModePhase Nonary.mode45 Nonary.counterPhase = refl

------------------------------------------------------------------------
-- 3. Compile the distinguished Fricke-like inertia element on the 18-block.
------------------------------------------------------------------------

compiledFrickeBlockAct :
  ∀ {source}
    {inertiaAttachment :
      DASHI.Moonshine.Base369Monster3BMultiplicityInertiaTwelveSeventyEightBidiExact.ActualMultiplicityInertiaAttachment source} ->
  NoGo.FineFrickeInertiaElement inertiaAttachment ->
  Nonary.ComplementMode5 ->
  ModeBlock18 ->
  ModeBlock18
compiledFrickeBlockAct
  {inertiaAttachment = inertiaAttachment}
  element mode (phase , sheet) =
  Nonary.flipBinaryPhase phase ,
  Outgoing.projectSecondary
    (Compiler.compiledTenByNineAct
      inertiaAttachment
      (NoGo.frickeInertia element)
      (embedModeBlock mode (phase , sheet)))

compiledFrickeBlockIntertwines :
  ∀ {source}
    {inertiaAttachment :
      DASHI.Moonshine.Base369Monster3BMultiplicityInertiaTwelveSeventyEightBidiExact.ActualMultiplicityInertiaAttachment source}
    (element : NoGo.FineFrickeInertiaElement inertiaAttachment)
    (mode : Nonary.ComplementMode5)
    (state : ModeBlock18) ->
  Compiler.compiledTenByNineAct
    inertiaAttachment
    (NoGo.frickeInertia element)
    (embedModeBlock mode state)
  ≡
  embedModeBlock mode
    (compiledFrickeBlockAct element mode state)
compiledFrickeBlockIntertwines
  {inertiaAttachment = inertiaAttachment}
  element mode (phase , sheet)
  with Compiler.compiledTenByNineAct
        inertiaAttachment
        (NoGo.frickeInertia element)
        (embedModeBlock mode (phase , sheet))
... | fine , secondary
  rewrite NoGo.fineProjectionIsFiniteFricke
            element
            (fineAtModePhase mode phase)
            sheet
        | fineFrickeAtModePhase mode phase
        | Outgoing.secondaryCodecRoundTrip secondary = refl

------------------------------------------------------------------------
-- 4. Recognition consequence.
------------------------------------------------------------------------

data NineStateSheetRemainsInvariantUnderFineFricke : Set where
data EighteenStateModeBlockRequiresMonsterAuthority : Set where

nineStateSheetCannotRemainInvariantUnderFineFricke :
  NineStateSheetRemainsInvariantUnderFineFricke -> ⊥
nineStateSheetCannotRemainInvariantUnderFineFricke ()

record Trialectic369OutgoingFrickeModeBlock18Boundary : Set where
  constructor trialectic-369-outgoing-fricke-mode-block18-boundary
  field
    binaryPhaseTimesSheet9BlockOwned : Bool
    blockCountEighteen : Bool
    finiteFrickePreservesMode : Bool
    finiteFrickeFlipsBinaryPhase : Bool
    frickeLikeElementBlockActionCompilerOwned : Bool
    blockIntertwiningGenerated : Bool
    actualMonsterFrickeElementRecognizedHere : Bool

canonicalTrialectic369OutgoingFrickeModeBlock18Boundary :
  Trialectic369OutgoingFrickeModeBlock18Boundary
canonicalTrialectic369OutgoingFrickeModeBlock18Boundary =
  trialectic-369-outgoing-fricke-mode-block18-boundary
    true true true true true true false
