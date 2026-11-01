module DASHI.Physics.Closure.NSTriadKNLuoHighLowDerivativePlacementTerminalExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Jean-Michel Bony; Hajer Bahouri; Jean-Yves Chemin;
-- Raphael Danchin.
-- Bony DOI: 10.24033/asens.1404.
-- Bahouri--Chemin--Danchin DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Construct the high--low derivative-placement cells rather than asking the
-- caller to provide a coefficient comparison.  For a separation gap,
--
--   derivative coefficient = (1/4)(1/2)^gap,
--
-- and the corrected low-shell weight is
--
--   (1/4)^gap + (1/4)(1/2)^gap.
--
-- The derivative coefficient is therefore below the corrected weight by the
-- nonnegative quarter-geometric term.  The resulting cells are fed directly
-- into the round-fourteen terminal Cauchy theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteHighLowDerivativeRatioExact as Ratio
import DASHI.Physics.Closure.NSTriadKNLuoFiniteHighLowCriticalKernelDominationExact as Kernel
import DASHI.Physics.Closure.NSTriadKNLuoFiniteHighLowTerminalClosureExact as Terminal

safeHighLowWeight : Nat → ℚ
safeHighLowWeight gap =
  Geo.pow Geo.quarter gap + Ratio.highLowDerivativeRatio gap

derivativeRatioBelowSafeWeight :
  (gap : Nat) →
  Ratio.highLowDerivativeRatio gap ≤ safeHighLowWeight gap
derivativeRatioBelowSafeWeight gap =
  let
    quarterPowerNN : 0ℚ ≤ Geo.pow Geo.quarter gap
    quarterPowerNN =
      Geo.powNonnegative Geo.quarter gap Geo.quarterNonnegative

    addQuarter :
      Ratio.highLowDerivativeRatio gap
      ≤ Geo.pow Geo.quarter gap + Ratio.highLowDerivativeRatio gap
    addQuarter =
      subst
        (λ lower →
          lower
          ≤ Geo.pow Geo.quarter gap
            + Ratio.highLowDerivativeRatio gap)
        (ℚₚ.+-identityˡ (Ratio.highLowDerivativeRatio gap))
        (ℚₚ.+-mono-≤ quarterPowerNN ℚₚ.≤-refl)
  in
  addQuarter

record HighLowDerivativeShell : Set where
  constructor high-low-derivative-shell
  field
    gap : Nat
    shellCriticalMass : ℚ
    shellCriticalMassNonnegative : 0ℚ ≤ shellCriticalMass

open HighLowDerivativeShell public

shellToKernelCell : HighLowDerivativeShell → Kernel.HighLowKernelCell
shellToKernelCell shell =
  Kernel.high-low-kernel-cell
    (Ratio.highLowDerivativeRatio (gap shell))
    (safeHighLowWeight (gap shell))
    (shellCriticalMass shell)
    (shellCriticalMassNonnegative shell)
    (derivativeRatioBelowSafeWeight (gap shell))

mapShells :
  List HighLowDerivativeShell →
  List Kernel.HighLowKernelCell
mapShells [] = []
mapShells (shell ∷ shells) =
  shellToKernelCell shell ∷ mapShells shells

record HighLowDerivativePlacementTerminalData : Set where
  constructor high-low-derivative-placement-terminal-data
  field
    shells : List HighLowDerivativeShell
    terminalPairs : List L2.Pair

    interactionSquared criticalEnvelopeSquared outputEnvelopeSquared : ℚ

    interactionMeaning :
      interactionSquared ≡ L2.square (L2.pairDot terminalPairs)

    terminalLeftMeaning :
      L2.leftNormSquared terminalPairs
      ≡ Kernel.sumDerivativeWeightedMass (mapShells shells)

    criticalEnvelopeNonnegative : 0ℚ ≤ criticalEnvelopeSquared
    outputEnvelopeNonnegative : 0ℚ ≤ outputEnvelopeSquared

    criticalMassBound :
      Kernel.sumCriticalWeightedMass (mapShells shells)
      ≤ criticalEnvelopeSquared

    outputMassBound :
      L2.rightNormSquared terminalPairs ≤ outputEnvelopeSquared

open HighLowDerivativePlacementTerminalData public

highLowDerivativePlacementTerminalSquareBound :
  (dataSet : HighLowDerivativePlacementTerminalData) →
  interactionSquared dataSet
  ≤ criticalEnvelopeSquared dataSet
    * outputEnvelopeSquared dataSet
highLowDerivativePlacementTerminalSquareBound dataSet =
  Terminal.finiteHighLowTerminalSquareBound
    (Terminal.high-low-terminal-closure-data
      (mapShells (shells dataSet))
      (terminalPairs dataSet)
      (interactionSquared dataSet)
      (criticalEnvelopeSquared dataSet)
      (outputEnvelopeSquared dataSet)
      (interactionMeaning dataSet)
      (terminalLeftMeaning dataSet)
      (criticalEnvelopeNonnegative dataSet)
      (outputEnvelopeNonnegative dataSet)
      (criticalMassBound dataSet)
      (outputMassBound dataSet))
