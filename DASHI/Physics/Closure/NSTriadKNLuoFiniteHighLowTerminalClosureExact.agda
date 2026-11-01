module DASHI.Physics.Closure.NSTriadKNLuoFiniteHighLowTerminalClosureExact where

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
-- Close the finite high--low terminal-window estimate after the corrected
-- derivative kernel has been inserted.  The proof composes:
--
-- * finite terminal Cauchy--Schwarz;
-- * the high--low derivative-weight mass;
-- * domination by the corrected critical low-shell kernel; and
-- * the critical/output envelope bounds.
--
-- The result is the radical-free square theorem
--
--   interaction_HL^2 <= criticalEnvelope^2 outputEnvelope^2.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteHighLowCriticalKernelDominationExact as HL

record HighLowTerminalClosureData : Set where
  constructor high-low-terminal-closure-data
  field
    kernelCells : List HL.HighLowKernelCell
    terminalPairs : List L2.Pair

    interactionSquared criticalEnvelopeSquared outputEnvelopeSquared : ℚ

    interactionMeaning :
      interactionSquared
      ≡ L2.square (L2.pairDot terminalPairs)

    terminalLeftMassMeaning :
      L2.leftNormSquared terminalPairs
      ≡ HL.sumDerivativeWeightedMass kernelCells

    criticalEnvelopeNonnegative : 0ℚ ≤ criticalEnvelopeSquared
    outputEnvelopeNonnegative : 0ℚ ≤ outputEnvelopeSquared

    criticalMassBound :
      HL.sumCriticalWeightedMass kernelCells
      ≤ criticalEnvelopeSquared

    outputMassBound :
      L2.rightNormSquared terminalPairs
      ≤ outputEnvelopeSquared

open HighLowTerminalClosureData public

terminalLeftCriticalBound :
  (dataSet : HighLowTerminalClosureData) →
  L2.leftNormSquared (terminalPairs dataSet)
  ≤ criticalEnvelopeSquared dataSet
terminalLeftCriticalBound dataSet =
  let
    derivativeToCritical :
      HL.sumDerivativeWeightedMass (kernelCells dataSet)
      ≤ criticalEnvelopeSquared dataSet
    derivativeToCritical =
      ℚₚ.≤-trans
        (HL.finiteHighLowCriticalKernelDomination
          (kernelCells dataSet))
        (criticalMassBound dataSet)
  in
  subst
    (λ lower → lower ≤ criticalEnvelopeSquared dataSet)
    (sym (terminalLeftMassMeaning dataSet))
    derivativeToCritical

finiteHighLowTerminalSquareBound :
  (dataSet : HighLowTerminalClosureData) →
  interactionSquared dataSet
  ≤ criticalEnvelopeSquared dataSet
      * outputEnvelopeSquared dataSet
finiteHighLowTerminalSquareBound dataSet =
  let
    cauchy :
      L2.square (L2.pairDot (terminalPairs dataSet))
      ≤ L2.leftNormSquared (terminalPairs dataSet)
        * L2.rightNormSquared (terminalPairs dataSet)
    cauchy = L2.finiteCauchySchwarzSquared (terminalPairs dataSet)

    envelopeProduct :
      L2.leftNormSquared (terminalPairs dataSet)
        * L2.rightNormSquared (terminalPairs dataSet)
      ≤ criticalEnvelopeSquared dataSet
        * outputEnvelopeSquared dataSet
    envelopeProduct =
      L2.nonnegativeProductMonotone
        (L2.leftNormSquaredNonnegative (terminalPairs dataSet))
        (L2.rightNormSquaredNonnegative (terminalPairs dataSet))
        (criticalEnvelopeNonnegative dataSet)
        (outputEnvelopeNonnegative dataSet)
        (terminalLeftCriticalBound dataSet)
        (outputMassBound dataSet)

    squared :
      L2.square (L2.pairDot (terminalPairs dataSet))
      ≤ criticalEnvelopeSquared dataSet
        * outputEnvelopeSquared dataSet
    squared = ℚₚ.≤-trans cauchy envelopeProduct
  in
  subst
    (λ lower →
      lower
      ≤ criticalEnvelopeSquared dataSet
        * outputEnvelopeSquared dataSet)
    (sym (interactionMeaning dataSet))
    squared
