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
-- Instantiate the round-six centered-kernel theorem with a canonical dyadic
-- two-point Littlewood--Paley prototype.  The kernel puts mass 1/2 at the
-- opposite displacements +/- 2^{-q}.  Its mass is one, its first moment is
-- exactly zero, its second moment is exactly 4^{-q}, and the second moment
-- quarters under q -> q+1.
--
-- The resulting centered Taylor sample is then sent through the existing
-- exact cancellation theorem.  This is a literal finite kernel
-- identification, not a declaration that the continuum LP kernel has already
-- been constructed.
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

kernelMass : ℚ
kernelMass = half + half

kernelMassOne : kernelMass ≡ 1ℚ
kernelMassOne = refl

firstMomentAt : Nat → ℚ
firstMomentAt shell =
  Even.firstMomentPair half (Near.windowRoot shell)

firstMomentAtZero :
  (shell : Nat) →
  firstMomentAt shell ≡ 0ℚ
firstMomentAtZero shell =
  Even.firstMomentPairCancels half (Near.windowRoot shell)

secondMomentAt : Nat → ℚ
secondMomentAt shell =
  half * L2.square (Near.windowRoot shell)
  + half * L2.square (- Near.windowRoot shell)

secondMomentMeaning :
  (shell : Nat) →
  secondMomentAt shell ≡ Near.windowLength shell
secondMomentMeaning shell =
  solve (Near.windowRoot shell ∷ [])

secondMomentQuarters :
  (shell : Nat) →
  secondMomentAt (suc shell)
  ≡ Geo.quarter * secondMomentAt shell
secondMomentQuarters shell =
  trans
    (secondMomentMeaning (suc shell))
    (trans
      (Near.windowLengthQuarters shell)
      (cong
        (Geo.quarter *_)
        (sym (secondMomentMeaning shell))))

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

canonicalCenteredCancellation :
  (center linear plusRemainder minusRemainder : ℚ) →
  Even.pairedCenteredIncrement
    (canonicalPairedTaylorSample
      center linear plusRemainder minusRemainder)
  ≡ Even.pairedRemainderContribution
    (canonicalPairedTaylorSample
      center linear plusRemainder minusRemainder)
canonicalCenteredCancellation center linear plusRemainder minusRemainder =
  Even.pairedTaylorLinearCancellation
    (canonicalPairedTaylorSample
      center linear plusRemainder minusRemainder)
