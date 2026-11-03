{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSVFMacroscopicSingleBranchRobustnessExact where

-- TSVF / TSFV: FINITE, SINGLE-SELECTED-BRANCH MACRO ROBUSTNESS.
--
-- Primary sources, with original authorship retained:
--   Aharonov, Cohen, Gruss, Landsberger (2014), "Measurement and Collapse
--   within the Two-State-Vector Formalism", DOI 10.1007/s40509-014-0011-9.
--   Aharonov, Cohen, Landsberger (2017), "The Two-Time Interpretation and
--   Macroscopic Time-Reversibility", DOI 10.3390/e19030111.
--
-- Original DASHI physical-history owner:
--   DASHI.Physics.Foundations.FiniteHistoryOrientationExact.
--
-- This module proves a nontrivial finite redundancy/erasure contrast:
--   (1) each explicitly selected pointer record has a three-bit encoding;
--   (2) every single-site flip alters microscopic code data;
--   (3) majority reconstructs the SAME pointer after any such disturbance;
--   (4) two different disturbance patterns are indistinguishable at the
--       macro output, so exact micro-recovery from that output is impossible;
--   (5) later boundary selections in the ORIGINAL DASHI history source
--       have the same earlier accessible past yet distinct hidden histories
--       and selected macroscopic pointer values;
--   (6) microscopic reversal-involution and macroscopic robustness coexist
--       without identifying the two operations.
--
-- This is a finite error-correction *analogue* of "classical robustness
-- under time-reversal", NOT a reproduction of the authors' quantum
-- post-selection overlap/rate argument or a proof of macroscopic time
-- reversal in nature. Here a disturbance is a flip, not unitary reversal.
-- Nor does a selected branch imply Everett worlds, universe creation,
-- entropy reversal, backward signalling, (3,1), YM or an OS mass gap.
--
-- Physical source missing: quantum boundary amplitudes and Born/ABL
-- normalization; pointer/environment overlap; robust N/n asymptotic;
-- same-state microscopic+macroscopic dynamics, limiting continuum and
-- physical same-clock/OS/YM reflection.
--
-- No local postulates, unsafe options, metas, terminating pragmas.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Foundations.FiniteHistoryOrientationExact as Micro

------------------------------------------------------------------------
-- Triple-redundancy, with explicit one-site disturbance.
------------------------------------------------------------------------

data Pointer : Set where
  pointerMinus : Pointer
  pointerPlus  : Pointer

data Bit : Set where
  bitMinus : Bit
  bitPlus  : Bit

data FaultSite : Set where
  faultFirst  : FaultSite
  faultMiddle : FaultSite
  faultLast   : FaultSite

data Triple : Set where
  triple : Bit → Bit → Bit → Triple

bitOf : Pointer → Bit
bitOf pointerMinus = bitMinus
bitOf pointerPlus  = bitPlus

pointerOf : Bit → Pointer
pointerOf bitMinus = pointerMinus
pointerOf bitPlus  = pointerPlus

encode : Pointer → Triple
encode p = triple (bitOf p) (bitOf p) (bitOf p)

flip : Bit → Bit
flip bitMinus = bitPlus
flip bitPlus  = bitMinus

singleFault : FaultSite → Triple → Triple
singleFault faultFirst  (triple a b c) = triple (flip a) b c
singleFault faultMiddle (triple a b c) = triple a (flip b) c
singleFault faultLast   (triple a b c) = triple a b (flip c)

majority : Bit → Bit → Bit → Bit
majority bitMinus bitMinus _        = bitMinus
majority bitPlus  bitPlus  _        = bitPlus
majority bitMinus bitPlus  bitMinus = bitMinus
majority bitMinus bitPlus  bitPlus  = bitPlus
majority bitPlus  bitMinus bitMinus = bitMinus
majority bitPlus  bitMinus bitPlus  = bitPlus

macroReadout : Triple → Pointer
macroReadout (triple a b c) = pointerOf (majority a b c)

unperturbedMacroReadout :
  (p : Pointer) → macroReadout (encode p) ≡ p
unperturbedMacroReadout pointerMinus = refl
unperturbedMacroReadout pointerPlus = refl

-- Nontrivial total theorem: both selected pointers, all three fault sites.
singleFaultMacroRobust :
  (p : Pointer) (fault : FaultSite) →
  macroReadout (singleFault fault (encode p)) ≡ p
singleFaultMacroRobust pointerMinus faultFirst  = refl
singleFaultMacroRobust pointerMinus faultMiddle = refl
singleFaultMacroRobust pointerMinus faultLast   = refl
singleFaultMacroRobust pointerPlus faultFirst   = refl
singleFaultMacroRobust pointerPlus faultMiddle  = refl
singleFaultMacroRobust pointerPlus faultLast    = refl

-- Sharp failure control: one flip is correctable, but two flips in the
-- same three-bit code can reverse the decoded macroscopic branch.
-- This blocks any claim of arbitrary-noise or universal reversal stability.
twoFaultsReverseSelectedMacro :
  macroReadout
    (singleFault faultMiddle
      (singleFault faultFirst (encode pointerMinus))) ≡ pointerPlus
twoFaultsReverseSelectedMacro = refl

twoFaultsDoNotPreserveOriginalPointer :
  macroReadout
    (singleFault faultMiddle
      (singleFault faultFirst (encode pointerMinus))) ≡ pointerMinus → ⊥
twoFaultsDoNotPreserveOriginalPointer ()

------------------------------------------------------------------------
-- At the fine representation level a single flip is never identical
-- to the unperturbed code. Restored macro record != restored microstate.
singleFaultChangesFineData :
  (p : Pointer) (fault : FaultSite) →
  singleFault fault (encode p) ≡ encode p → ⊥
singleFaultChangesFineData pointerMinus faultFirst  ()
singleFaultChangesFineData pointerMinus faultMiddle ()
singleFaultChangesFineData pointerMinus faultLast   ()
singleFaultChangesFineData pointerPlus faultFirst   ()
singleFaultChangesFineData pointerPlus faultMiddle  ()
singleFaultChangesFineData pointerPlus faultLast    ()

firstAndLastFineDataDiffer :
  singleFault faultFirst (encode pointerMinus) ≡
  singleFault faultLast (encode pointerMinus) → ⊥
firstAndLastFineDataDiffer ()

-- Even exact knowledge of the selected macroscopic pointer after a
-- single fault cannot recover which fine disturbance took place.
-- This is the appropriate reverse noninjectivity result.
noExactMicroRestorationFromMacro :
  (recover : Pointer → Triple) →
  ((fault : FaultSite) →
    recover (macroReadout (singleFault fault (encode pointerMinus)))
      ≡ singleFault fault (encode pointerMinus)) →
  ⊥
noExactMicroRestorationFromMacro recover correct =
  firstAndLastFineDataDiffer
    (trans (sym (correct faultFirst))
      (trans
        (cong recover
          (trans (singleFaultMacroRobust pointerMinus faultFirst)
            (sym (singleFaultMacroRobust pointerMinus faultLast))))
        (correct faultLast)))

------------------------------------------------------------------------
-- Reuse the ORIGINAL two-boundary history carrier rather than add a
-- parallel history theory. A selected macro branch can depend on the
-- later physical boundary, without changing earlier accessible data.
------------------------------------------------------------------------

selectedPointer : Micro.LaterChoice → Pointer
selectedPointer Micro.chooseMinusBoundary = pointerMinus
selectedPointer Micro.choosePlusBoundary = pointerPlus

originalPastRecordUnchanged :
  Micro.pastAccessibleOutcome Micro.chooseMinusBoundary ≡
  Micro.pastAccessibleOutcome Micro.choosePlusBoundary
originalPastRecordUnchanged = Micro.finiteNoBackwardSignalling

originalMicroHistoriesDiffer :
  Micro.hiddenHistory Micro.chooseMinusBoundary ≡
  Micro.hiddenHistory Micro.choosePlusBoundary → ⊥
originalMicroHistoriesDiffer =
  Micro.futureBoundaryCanChangeHiddenHistory

selectedPointersDiffer :
  selectedPointer Micro.chooseMinusBoundary ≡
  selectedPointer Micro.choosePlusBoundary → ⊥
selectedPointersDiffer ()

originalActionAgreesUnderReversal :
  (h : Micro.History2) →
  Micro.historyAction (Micro.reverseHistory h) ≡ Micro.historyAction h
originalActionAgreesUnderReversal = Micro.actionTimeReversalInvariant

microReversalInvolutive :
  (h : Micro.History2) →
  Micro.reverseHistory (Micro.reverseHistory h) ≡ h
microReversalInvolutive = Micro.reverseHistoryInvolutive

selectedBranchMacroRobust :
  (choice : Micro.LaterChoice) (fault : FaultSite) →
  macroReadout
    (singleFault fault (encode (selectedPointer choice)))
  ≡ selectedPointer choice
selectedBranchMacroRobust choice fault =
  singleFaultMacroRobust (selectedPointer choice) fault

-- Same past cannot select one of the two macro branches from the past
-- record alone. This is a genuine source-owner counterexample.
pastOnlyCannotDetermineSelectedMacroBranch :
  (recover : Micro.PastRecord → Pointer) →
  ((choice : Micro.LaterChoice) →
    recover (Micro.pastAccessibleOutcome choice) ≡ selectedPointer choice) →
  ⊥
pastOnlyCannotDetermineSelectedMacroBranch recover correct =
  selectedPointersDiffer
    (trans (sym (correct Micro.chooseMinusBoundary))
      (trans
        (cong recover originalPastRecordUnchanged)
        (correct Micro.choosePlusBoundary)))

-- One explicit combined finite theorem: microscopic reversible action
-- and restoration of the selected macro pointer under one-site corruption
-- are COMPATIBLE, though logically different properties.
reversalAndRobustMacroCoexist :
  (h : Micro.History2) →
  (choice : Micro.LaterChoice) →
  (fault : FaultSite) →
  (Micro.reverseHistory (Micro.reverseHistory h) ≡ h)
  ×
  (macroReadout (singleFault fault (encode (selectedPointer choice)))
    ≡ selectedPointer choice)
reversalAndRobustMacroCoexist h choice fault =
  microReversalInvolutive h , selectedBranchMacroRobust choice fault
