module DASHI.Physics.Closure.NSTriadKNLuoFiniteHighHighTerminalCauchyExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Title: finite Cauchy--Schwarz inequality.
-- DOI: not applicable to the nineteenth-century result.
--
-- Harmonic-analysis reference:
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Close the finite terminal-window Cauchy step behind HH3.  The paired list
-- represents time/shell cells after the high--high producer and gap weights
-- have been inserted.  If the left squared mass is bounded by the critical
-- envelope and the right squared mass by the output-energy envelope, then
--
--   interaction^2 <= criticalEnvelope^2 outputEnvelope^2.
--
-- This is the radical-free square form of |N_q^HH| <= C_HH A_q E_q.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using (List)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

record HighHighTerminalCauchyData : Set where
  constructor high-high-terminal-cauchy-data
  field
    terminalPairs : List L2.Pair
    interactionSquared criticalEnvelopeSquared outputEnvelopeSquared : ℚ

    interactionMeaning :
      interactionSquared ≡ L2.square (L2.pairDot terminalPairs)

    criticalEnvelopeNonnegative :
      0ℚ ≤ criticalEnvelopeSquared

    outputEnvelopeNonnegative :
      0ℚ ≤ outputEnvelopeSquared

    criticalMassBound :
      L2.leftNormSquared terminalPairs ≤ criticalEnvelopeSquared

    outputMassBound :
      L2.rightNormSquared terminalPairs ≤ outputEnvelopeSquared

open HighHighTerminalCauchyData public

finiteHighHighTerminalSquareBound :
  (dataSet : HighHighTerminalCauchyData) →
  interactionSquared dataSet
  ≤ criticalEnvelopeSquared dataSet * outputEnvelopeSquared dataSet
finiteHighHighTerminalSquareBound dataSet =
  let
    cauchy :
      L2.square (L2.pairDot (terminalPairs dataSet))
      ≤ L2.leftNormSquared (terminalPairs dataSet)
        * L2.rightNormSquared (terminalPairs dataSet)
    cauchy = L2.finiteCauchySchwarzSquared (terminalPairs dataSet)

    envelopeProduct :
      L2.leftNormSquared (terminalPairs dataSet)
        * L2.rightNormSquared (terminalPairs dataSet)
      ≤ criticalEnvelopeSquared dataSet * outputEnvelopeSquared dataSet
    envelopeProduct =
      L2.nonnegativeProductMonotone
        (L2.leftNormSquaredNonnegative (terminalPairs dataSet))
        (L2.rightNormSquaredNonnegative (terminalPairs dataSet))
        (criticalEnvelopeNonnegative dataSet)
        (outputEnvelopeNonnegative dataSet)
        (criticalMassBound dataSet)
        (outputMassBound dataSet)

    squaredBound :
      L2.square (L2.pairDot (terminalPairs dataSet))
      ≤ criticalEnvelopeSquared dataSet * outputEnvelopeSquared dataSet
    squaredBound = ℚₚ.≤-trans cauchy envelopeProduct
  in
  subst
    (λ lower →
      lower
      ≤ criticalEnvelopeSquared dataSet * outputEnvelopeSquared dataSet)
    (sym (interactionMeaning dataSet))
    squaredBound
