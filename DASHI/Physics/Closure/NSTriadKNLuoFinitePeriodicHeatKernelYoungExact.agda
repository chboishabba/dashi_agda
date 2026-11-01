module DASHI.Physics.Closure.NSTriadKNLuoFinitePeriodicHeatKernelYoungExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Darko Mitrović.
-- Title: "A High-Frequency Tail Condition and a Diagnostic Iteration for
-- the Navier--Stokes Equations".
-- arXiv:2411.02568.
-- DOI: none assigned in the cited preprint version.
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- Proceedings of the Royal Society of London. Series A 87 (1912).
-- DOI: 10.1098/rspa.1912.0086.
--
-- PURPOSE
-- Compose the repository's genuine finite signed-convolution Young theorem
-- with the exact dyadic heat factor.  If a finite periodic kernel already has
-- a two-sided Young majorant C, then applying one common nonnegative heat
-- factor h(gap) to every mode gives the exact two-sided bound
--
--   |sum dampedTerm| <= h(gap) C.
--
-- This proves the finite periodic operator step.  The continuum torus leaf is
-- now specifically the proof that the literal Fourier heat kernel supplies
-- the base finite Young data uniformly in the cutoff.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _*_; -_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Sum
import DASHI.Physics.Closure.NSTriadKNLuoFiniteSignedConvolutionYoungExact as Young
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicHeatDampingExact as Heat
import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo

halfNonnegative : 0ℚ ≤ Heat.half
halfNonnegative = toWitness {a? = 0ℚ ≤? Heat.half} _

record FinitePeriodicHeatKernelData : Set where
  constructor finite-periodic-heat-kernel
  field
    baseYoungData : Young.FiniteSignedConvolutionYoungData
    terminalGap : Nat

open FinitePeriodicHeatKernelData public

heatFactor : FinitePeriodicHeatKernelData → ℚ
heatFactor inputs = Heat.heatDamping (terminalGap inputs)

dampedSignedTerm : FinitePeriodicHeatKernelData → Nat → ℚ
dampedSignedTerm inputs index =
  heatFactor inputs * Young.signedTerm (baseYoungData inputs) index

dampedPositiveTerm : FinitePeriodicHeatKernelData → Nat → ℚ
dampedPositiveTerm inputs index =
  heatFactor inputs * Young.positiveTermMajorant (baseYoungData inputs) index

heatFactorNonnegative :
  (inputs : FinitePeriodicHeatKernelData) →
  0ℚ ≤ heatFactor inputs
heatFactorNonnegative inputs =
  Geo.powNonnegative
    Heat.half
    (terminalGap inputs)
    halfNonnegative

dampedTermUpper :
  (inputs : FinitePeriodicHeatKernelData) →
  (index : Nat) →
  dampedSignedTerm inputs index ≤ dampedPositiveTerm inputs index
dampedTermUpper inputs index =
  let
    instance
      heatIsNonnegative = nonNegative (heatFactorNonnegative inputs)
  in
  ℚₚ.*-monoˡ-≤-nonNeg
    (heatFactor inputs)
    (Young.termUpper (baseYoungData inputs) index)

dampedTermLower :
  (inputs : FinitePeriodicHeatKernelData) →
  (index : Nat) →
  - dampedPositiveTerm inputs index ≤ dampedSignedTerm inputs index
dampedTermLower inputs index =
  let
    scaled :
      heatFactor inputs
        * (- Young.positiveTermMajorant (baseYoungData inputs) index)
      ≤ heatFactor inputs
        * Young.signedTerm (baseYoungData inputs) index
    scaled =
      let
        instance
          heatIsNonnegative = nonNegative (heatFactorNonnegative inputs)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (heatFactor inputs)
        (Young.termLower (baseYoungData inputs) index)

    leftMeaning :
      heatFactor inputs
        * (- Young.positiveTermMajorant (baseYoungData inputs) index)
      ≡ - dampedPositiveTerm inputs index
    leftMeaning =
      solve
        ( heatFactor inputs
        ∷ Young.positiveTermMajorant (baseYoungData inputs) index
        ∷ []
        )
  in
  subst
    (λ lower → lower ≤ dampedSignedTerm inputs index)
    leftMeaning
    scaled

dampedPositivePrefixBound :
  (inputs : FinitePeriodicHeatKernelData) →
  Sum.sumTo
    (dampedPositiveTerm inputs)
    (Young.cutoff (baseYoungData inputs))
  ≤ heatFactor inputs * Young.l1TimesSupBound (baseYoungData inputs)
dampedPositivePrefixBound inputs =
  let
    baseBound =
      Young.positiveMajorantPrefixBound (baseYoungData inputs)

    scaledBound :
      heatFactor inputs
        * Sum.sumTo
            (Young.positiveTermMajorant (baseYoungData inputs))
            (Young.cutoff (baseYoungData inputs))
      ≤ heatFactor inputs * Young.l1TimesSupBound (baseYoungData inputs)
    scaledBound =
      let
        instance
          heatIsNonnegative = nonNegative (heatFactorNonnegative inputs)
      in
      ℚₚ.*-monoˡ-≤-nonNeg (heatFactor inputs) baseBound
  in
  subst
    (λ lower →
      lower
      ≤ heatFactor inputs * Young.l1TimesSupBound (baseYoungData inputs))
    (sym
      (Sum.scaleSum
        (heatFactor inputs)
        (Young.positiveTermMajorant (baseYoungData inputs))
        (Young.cutoff (baseYoungData inputs))))
    scaledBound

dampedYoungData :
  FinitePeriodicHeatKernelData → Young.FiniteSignedConvolutionYoungData
dampedYoungData inputs = Young.finite-young
  (dampedSignedTerm inputs)
  (dampedPositiveTerm inputs)
  (Young.cutoff (baseYoungData inputs))
  (dampedTermUpper inputs)
  (dampedTermLower inputs)
  (heatFactor inputs * Young.l1TimesSupBound (baseYoungData inputs))
  (dampedPositivePrefixBound inputs)

finitePeriodicHeatKernelUpper :
  (inputs : FinitePeriodicHeatKernelData) →
  Sum.sumTo
    (dampedSignedTerm inputs)
    (Young.cutoff (baseYoungData inputs))
  ≤ heatFactor inputs * Young.l1TimesSupBound (baseYoungData inputs)
finitePeriodicHeatKernelUpper inputs =
  Young.finiteConvolutionUpper (dampedYoungData inputs)

finitePeriodicHeatKernelLower :
  (inputs : FinitePeriodicHeatKernelData) →
  - (heatFactor inputs * Young.l1TimesSupBound (baseYoungData inputs))
  ≤ Sum.sumTo
      (dampedSignedTerm inputs)
      (Young.cutoff (baseYoungData inputs))
finitePeriodicHeatKernelLower inputs =
  Young.finiteConvolutionLower (dampedYoungData inputs)
