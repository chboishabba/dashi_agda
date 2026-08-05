module DASHI.Physics.Closure.NSTriadKNLuoFiniteLittlewoodPaleyMomentIdentificationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- Communications in Mathematical Physics 165 (1994), 207--209.
-- DOI: 10.1007/BF02099744.
--
-- PURPOSE
-- Instantiate the round-six centered-kernel theorem with the canonical signed
-- three-point dyadic bandpass stencil
--
--   K_q = 1/2 delta_{h_q} + 1/2 delta_{-h_q} - delta_0,
--   h_q = 2^{-q}.
--
-- Unlike a positive mollifier, this stencil has the cancellation required of
-- a Littlewood--Paley bandpass prototype:
--
--   mass(K_q)=0,
--   firstMoment(K_q)=0,
--   secondMoment(K_q)=4^{-q}.
--
-- Its action is exactly one half of the centered second difference, so the
-- existing paired Taylor theorem removes the linear term and leaves only the
-- second-order remainder.  The second moment quarters under q -> q+1.
--
-- This is a literal finite bandpass stencil.  Identification with a selected
-- smooth continuum LP kernel still requires its Fourier support, scaling and
-- moment integrals on the official torus carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteEvenKernelCenteredTaylorExact as Even
import DASHI.Physics.Closure.NSTriadKNLuoFiniteNearWindowHalfKernelExact as Near
import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

half : ℚ
half = Int.+ 1 / 2

centerWeight : ℚ
centerWeight = - 1ℚ

bandpassMass : ℚ
bandpassMass = half + half + centerWeight

bandpassMassZero : bandpassMass ≡ 0ℚ
bandpassMassZero = solve []

bandpassFirstMoment : Nat → ℚ
bandpassFirstMoment shell =
  half * Near.windowRoot shell
  + half * (- Near.windowRoot shell)
  + centerWeight * 0ℚ

bandpassFirstMomentZero :
  (shell : Nat) →
  bandpassFirstMoment shell ≡ 0ℚ
bandpassFirstMomentZero shell =
  solve (Near.windowRoot shell ∷ [])

bandpassSecondMoment : Nat → ℚ
bandpassSecondMoment shell =
  half * L2.square (Near.windowRoot shell)
  + half * L2.square (- Near.windowRoot shell)
  + centerWeight * L2.square 0ℚ

bandpassSecondMomentMeaning :
  (shell : Nat) →
  bandpassSecondMoment shell ≡ Near.windowLength shell
bandpassSecondMomentMeaning shell =
  solve (Near.windowRoot shell ∷ [])

bandpassSecondMomentQuarters :
  (shell : Nat) →
  bandpassSecondMoment (suc shell)
  ≡ Geo.quarter * bandpassSecondMoment shell
bandpassSecondMomentQuarters shell =
  trans
    (bandpassSecondMomentMeaning (suc shell))
    (trans
      (Near.windowLengthQuarters shell)
      (cong
        (Geo.quarter *_)
        (sym (bandpassSecondMomentMeaning shell))))

bandpassAction : ℚ → ℚ → ℚ → ℚ
bandpassAction center plusValue minusValue =
  half * plusValue + half * minusValue + centerWeight * center

bandpassActionCenteredMeaning :
  (center plusValue minusValue : ℚ) →
  bandpassAction center plusValue minusValue
  ≡ half * (plusValue + (- center))
    + half * (minusValue + (- center))
bandpassActionCenteredMeaning center plusValue minusValue =
  solve (center ∷ plusValue ∷ minusValue ∷ [])

canonicalPairedTaylorSample :
  (center linear plusRemainder minusRemainder : ℚ) →
  Even.PairedTaylorSample
canonicalPairedTaylorSample center linear plusRemainder minusRemainder =
  Even.paired-taylor-sample
    half
    center
    linear
    plusRemainder
    minusRemainder
    (center + linear + plusRemainder)
    (center + (- linear) + minusRemainder)
    refl
    (solve
      ( center
      ∷ linear
      ∷ minusRemainder
      ∷ []
      ))

bandpassActionIsPairedCenteredIncrement :
  (center linear plusRemainder minusRemainder : ℚ) →
  bandpassAction
    center
    (center + linear + plusRemainder)
    (center + (- linear) + minusRemainder)
  ≡ Even.pairedCenteredIncrement
      (canonicalPairedTaylorSample
        center linear plusRemainder minusRemainder)
bandpassActionIsPairedCenteredIncrement
  center linear plusRemainder minusRemainder =
  solve (center ∷ linear ∷ plusRemainder ∷ minusRemainder ∷ [])

canonicalBandpassRemainderIdentity :
  (center linear plusRemainder minusRemainder : ℚ) →
  bandpassAction
    center
    (center + linear + plusRemainder)
    (center + (- linear) + minusRemainder)
  ≡ Even.pairedRemainderContribution
      (canonicalPairedTaylorSample
        center linear plusRemainder minusRemainder)
canonicalBandpassRemainderIdentity
  center linear plusRemainder minusRemainder =
  trans
    (bandpassActionIsPairedCenteredIncrement
      center linear plusRemainder minusRemainder)
    (Even.pairedTaylorLinearCancellation
      (canonicalPairedTaylorSample
        center linear plusRemainder minusRemainder))
