module DASHI.Physics.Closure.NSTriadKNLuoLowHighSixThreeTerminalExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Jean-Michel Bony; Hajer Bahouri; Jean-Yves Chemin;
-- Raphael Danchin.
-- Bony DOI: 10.24033/asens.1404.
-- Bahouri--Chemin--Danchin DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Title: finite Cauchy--Schwarz inequality.
-- DOI: not applicable to the nineteenth-century result.
--
-- PURPOSE
-- Carry the complete finite (L6,L3) two-branch shell budget through the
-- terminal-window Cauchy estimate.  This is the radical-free LH theorem after
-- the centered kernel cells have been constructed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using (List)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteSixThreeCommutatorBudgetExact as Budget
import DASHI.Physics.Closure.NSTriadKNLuoSixThreeCenteredCommutatorScaleExact as Scale

record LowHighSixThreeTerminalData : Set where
  constructor low-high-six-three-terminal-data
  field
    commutatorCells : List Budget.SixThreeCommutatorCell
    terminalPairs : List L2.Pair

    interactionSquared criticalEnvelopeSquared outputEnvelopeSquared : ℚ

    interactionMeaning :
      interactionSquared ≡ L2.square (L2.pairDot terminalPairs)

    terminalLeftMeaning :
      L2.leftNormSquared terminalPairs
      ≡ Budget.sumCellCommutatorSquared commutatorCells

    criticalEnvelopeNonnegative : 0ℚ ≤ criticalEnvelopeSquared
    outputEnvelopeNonnegative : 0ℚ ≤ outputEnvelopeSquared

    weakGapEnvelopeBound :
      Scale.two * Budget.sumWeakCellEnvelope commutatorCells
      ≤ criticalEnvelopeSquared

    outputMassBound :
      L2.rightNormSquared terminalPairs ≤ outputEnvelopeSquared

open LowHighSixThreeTerminalData public

lowHighCriticalMassBound :
  (dataSet : LowHighSixThreeTerminalData) →
  L2.leftNormSquared (terminalPairs dataSet)
  ≤ criticalEnvelopeSquared dataSet
lowHighCriticalMassBound dataSet =
  let
    shellBudget :
      Budget.sumCellCommutatorSquared (commutatorCells dataSet)
      ≤ Scale.two
        * Budget.sumWeakCellEnvelope (commutatorCells dataSet)
    shellBudget =
      Budget.finiteSixThreeCommutatorBudget
        (commutatorCells dataSet)

    toEnvelope :
      Budget.sumCellCommutatorSquared (commutatorCells dataSet)
      ≤ criticalEnvelopeSquared dataSet
    toEnvelope =
      ℚₚ.≤-trans shellBudget (weakGapEnvelopeBound dataSet)
  in
  subst
    (λ lower → lower ≤ criticalEnvelopeSquared dataSet)
    (sym (terminalLeftMeaning dataSet))
    toEnvelope

lowHighSixThreeTerminalSquareBound :
  (dataSet : LowHighSixThreeTerminalData) →
  interactionSquared dataSet
  ≤ criticalEnvelopeSquared dataSet
    * outputEnvelopeSquared dataSet
lowHighSixThreeTerminalSquareBound dataSet =
  let
    cauchy = L2.finiteCauchySchwarzSquared (terminalPairs dataSet)

    envelopeProduct =
      L2.nonnegativeProductMonotone
        (L2.leftNormSquaredNonnegative (terminalPairs dataSet))
        (L2.rightNormSquaredNonnegative (terminalPairs dataSet))
        (criticalEnvelopeNonnegative dataSet)
        (outputEnvelopeNonnegative dataSet)
        (lowHighCriticalMassBound dataSet)
        (outputMassBound dataSet)

    combined = ℚₚ.≤-trans cauchy envelopeProduct
  in
  subst
    (λ lower →
      lower
      ≤ criticalEnvelopeSquared dataSet
        * outputEnvelopeSquared dataSet)
    (sym (interactionMeaning dataSet))
    combined
