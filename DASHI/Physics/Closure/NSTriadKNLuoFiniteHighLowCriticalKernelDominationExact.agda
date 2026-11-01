module DASHI.Physics.Closure.NSTriadKNLuoFiniteHighLowCriticalKernelDominationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Jean-Michel Bony; Hajer Bahouri; Jean-Yves Chemin;
-- Raphael Danchin.
-- Bony DOI: 10.24033/asens.1404.
-- Bahouri--Chemin--Danchin DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Close the finite ordered step in HL2.  Once every high--low derivative
-- coefficient is dominated by the corrected critical low-shell weight, the
-- complete weighted derivative mass is dominated by the critical functional.
-- The continuum paraproduct estimate remains the producer of the cellwise
-- coefficient comparison and shell masses.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ

record HighLowKernelCell : Set where
  constructor high-low-kernel-cell
  field
    derivativeCoefficient criticalWeight shellCriticalMass : ℚ
    shellMassNonnegative : 0ℚ ≤ shellCriticalMass
    derivativeCoefficientBound :
      derivativeCoefficient ≤ criticalWeight

open HighLowKernelCell public

derivativeWeightedMass : HighLowKernelCell → ℚ
derivativeWeightedMass cell =
  derivativeCoefficient cell * shellCriticalMass cell

criticalWeightedMass : HighLowKernelCell → ℚ
criticalWeightedMass cell =
  criticalWeight cell * shellCriticalMass cell

cellKernelDomination :
  (cell : HighLowKernelCell) →
  derivativeWeightedMass cell ≤ criticalWeightedMass cell
cellKernelDomination cell =
  let
    instance
      shellMassIsNonnegative =
        nonNegative (shellMassNonnegative cell)
  in
  ℚₚ.*-monoʳ-≤-nonNeg
    (shellCriticalMass cell)
    (derivativeCoefficientBound cell)

sumDerivativeWeightedMass : List HighLowKernelCell → ℚ
sumDerivativeWeightedMass [] = 0ℚ
sumDerivativeWeightedMass (cell ∷ cells) =
  derivativeWeightedMass cell + sumDerivativeWeightedMass cells

sumCriticalWeightedMass : List HighLowKernelCell → ℚ
sumCriticalWeightedMass [] = 0ℚ
sumCriticalWeightedMass (cell ∷ cells) =
  criticalWeightedMass cell + sumCriticalWeightedMass cells

finiteHighLowCriticalKernelDomination :
  (cells : List HighLowKernelCell) →
  sumDerivativeWeightedMass cells ≤ sumCriticalWeightedMass cells
finiteHighLowCriticalKernelDomination [] = ℚₚ.≤-refl
finiteHighLowCriticalKernelDomination (cell ∷ cells) =
  ℚₚ.+-mono-≤
    (cellKernelDomination cell)
    (finiteHighLowCriticalKernelDomination cells)
