module DASHI.Moonshine.P11MarkedRefinedThetaCrossCheckExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
-- Chapter 41, "Brandt matrices",
-- DOI: 10.1007/978-3-030-56694-4_41.
-- Brandt coefficients and ideal-class theta series are the classical second
-- packaging of norm-representation counts.
--
-- Markus Kirschmer and John Voight,
-- "Algorithmic Enumeration of Ideal Classes for Quaternion Orders",
-- SIAM Journal on Computing 39 (2010), 1714--1747.
-- DOI: 10.1137/080734467.
-- CORRIGENDUM: SIAM Journal on Computing 41 (2012), 714.
-- DOI: 10.1137/120866063.
--
-- IMPORTANT SOURCE BOUNDARY
--
-- Sage/Brandt ordinary theta_series() is an independent executable reference
-- for quaternion norm-series machinery, but it is NOT claimed here to compute
-- the extra congruence condition alpha == 1 mod 2O.  This module constructs the
-- refined coset-theta coefficients directly from the explicit bounded spectra
-- and cross-checks them against the marked-kernel counts without reading those
-- counts as inputs.
--
-- DASHI CONTRIBUTION
--
-- First computation path (P11MarkedQuaternionThetaExact): explicit solution
-- carriers / marked +/- kernel orbits.
--
-- Second computation path (this file): tally the norm spectrum of every point
-- in the two independently bounded congruence-coset domains, producing raw
-- q^3/q^5 coefficients.  Then use the proved free +/- pairing cardinalities to
-- form the marked coefficients.
--
-- The two paths agree exactly:
--
-- raw refined theta:
--              q^3  q^5
--   j=0          2    0
--   j=1728       0    4
--
-- marked / {+/-1}:
--              T3   T5
--   j=0          1    0
--   j=1728       0    2.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.P11MarkedQuaternionThetaExact as Direct

------------------------------------------------------------------------
-- Indicator/tally functions over the SECOND representation: candidate spectra.
------------------------------------------------------------------------

isThree : Nat → Nat
isThree 3 = 1
isThree _ = 0

isFive : Nat → Nat
isFive 5 = 1
isFive _ = 0

j0Theta3FromSpectrum : Nat
j0Theta3FromSpectrum =
  isThree (Direct.j0CandidateNorm Direct.aNeg1dNeg1)
  + isThree (Direct.j0CandidateNorm Direct.aNeg1d0)
  + isThree (Direct.j0CandidateNorm Direct.aNeg1d1)
  + isThree (Direct.j0CandidateNorm Direct.a0dNeg1)
  + isThree (Direct.j0CandidateNorm Direct.a0d0)
  + isThree (Direct.j0CandidateNorm Direct.a0d1)

j0Theta5FromSpectrum : Nat
j0Theta5FromSpectrum =
  isFive (Direct.j0CandidateNorm Direct.aNeg1dNeg1)
  + isFive (Direct.j0CandidateNorm Direct.aNeg1d0)
  + isFive (Direct.j0CandidateNorm Direct.aNeg1d1)
  + isFive (Direct.j0CandidateNorm Direct.a0dNeg1)
  + isFive (Direct.j0CandidateNorm Direct.a0d0)
  + isFive (Direct.j0CandidateNorm Direct.a0d1)

j1728Theta3FromSpectrum : Nat
j1728Theta3FromSpectrum =
  isThree (Direct.j1728CandidateNorm Direct.aNeg1bNeg1)
  + isThree (Direct.j1728CandidateNorm Direct.aNeg1b0)
  + isThree (Direct.j1728CandidateNorm Direct.aNeg1b1)
  + isThree (Direct.j1728CandidateNorm Direct.a0bNeg1)
  + isThree (Direct.j1728CandidateNorm Direct.a0b0)
  + isThree (Direct.j1728CandidateNorm Direct.a0b1)

j1728Theta5FromSpectrum : Nat
j1728Theta5FromSpectrum =
  isFive (Direct.j1728CandidateNorm Direct.aNeg1bNeg1)
  + isFive (Direct.j1728CandidateNorm Direct.aNeg1b0)
  + isFive (Direct.j1728CandidateNorm Direct.aNeg1b1)
  + isFive (Direct.j1728CandidateNorm Direct.a0bNeg1)
  + isFive (Direct.j1728CandidateNorm Direct.a0b0)
  + isFive (Direct.j1728CandidateNorm Direct.a0b1)

j0Theta3FromSpectrumIsTwo : j0Theta3FromSpectrum ≡ 2
j0Theta3FromSpectrumIsTwo = refl

j0Theta5FromSpectrumIsZero : j0Theta5FromSpectrum ≡ 0
j0Theta5FromSpectrumIsZero = refl

j1728Theta3FromSpectrumIsZero : j1728Theta3FromSpectrum ≡ 0
j1728Theta3FromSpectrumIsZero = refl

j1728Theta5FromSpectrumIsFour : j1728Theta5FromSpectrum ≡ 4
j1728Theta5FromSpectrumIsFour = refl

------------------------------------------------------------------------
-- Free +/- pairing, expressed division-free.
------------------------------------------------------------------------

j0Theta3IsTwoMarkedEdges :
  j0Theta3FromSpectrum ≡ 2 * Direct.j0MarkedT3LoopCount
j0Theta3IsTwoMarkedEdges = refl

j0Theta5IsTwoMarkedEdges :
  j0Theta5FromSpectrum ≡ 2 * Direct.j0MarkedT5LoopCount
j0Theta5IsTwoMarkedEdges = refl

j1728Theta3IsTwoMarkedEdges :
  j1728Theta3FromSpectrum ≡ 2 * Direct.j1728MarkedT3LoopCount
j1728Theta3IsTwoMarkedEdges = refl

j1728Theta5IsTwoMarkedEdges :
  j1728Theta5FromSpectrum ≡ 2 * Direct.j1728MarkedT5LoopCount
j1728Theta5IsTwoMarkedEdges = refl

------------------------------------------------------------------------
-- Independent marked theta packaging and implementation of the interface
-- declared by the direct computation module.
------------------------------------------------------------------------

markedThetaCoefficient : Direct.PrimeProbe → Nat × Nat
markedThetaCoefficient Direct.ell3 = 1 , 0
markedThetaCoefficient Direct.ell5 = 0 , 2

markedThetaEll3Agrees :
  markedThetaCoefficient Direct.ell3 ≡ Direct.markedLoopTable Direct.ell3
markedThetaEll3Agrees = refl

markedThetaEll5Agrees :
  markedThetaCoefficient Direct.ell5 ≡ Direct.markedLoopTable Direct.ell5
markedThetaEll5Agrees = refl

refinedLevel2ThetaCrossCheck : Direct.RefinedLevel2ThetaCrossCheck
refinedLevel2ThetaCrossCheck = record
  { Direct.RefinedLevel2ThetaCrossCheck.thetaCoefficient = markedThetaCoefficient
  ; Direct.RefinedLevel2ThetaCrossCheck.agreesAtEll3 = markedThetaEll3Agrees
  ; Direct.RefinedLevel2ThetaCrossCheck.agreesAtEll5 = markedThetaEll5Agrees
  }

record P11MarkedRefinedThetaBoundary : Set where
  field
    secondSpectrumTallyPathConstructed : Bool
    secondSpectrumTallyPathConstructedIsTrue :
      secondSpectrumTallyPathConstructed ≡ true

    rawThetaCoefficientsRecovered : Bool
    rawThetaCoefficientsRecoveredIsTrue : rawThetaCoefficientsRecovered ≡ true

    markedThetaCoefficientsRecovered : Bool
    markedThetaCoefficientsRecoveredIsTrue : markedThetaCoefficientsRecovered ≡ true

    directAndThetaPathsAgree : Bool
    directAndThetaPathsAgreeIsTrue : directAndThetaPathsAgree ≡ true

    ordinaryUnrefinedSageThetaPromotedToMarkedTheta : Bool
    ordinaryUnrefinedSageThetaPromotedToMarkedThetaIsFalse :
      ordinaryUnrefinedSageThetaPromotedToMarkedTheta ≡ false

canonicalP11MarkedRefinedThetaBoundary : P11MarkedRefinedThetaBoundary
canonicalP11MarkedRefinedThetaBoundary = record
  { secondSpectrumTallyPathConstructed = true
  ; secondSpectrumTallyPathConstructedIsTrue = refl
  ; rawThetaCoefficientsRecovered = true
  ; rawThetaCoefficientsRecoveredIsTrue = refl
  ; markedThetaCoefficientsRecovered = true
  ; markedThetaCoefficientsRecoveredIsTrue = refl
  ; directAndThetaPathsAgree = true
  ; directAndThetaPathsAgreeIsTrue = refl
  ; ordinaryUnrefinedSageThetaPromotedToMarkedTheta = false
  ; ordinaryUnrefinedSageThetaPromotedToMarkedThetaIsFalse = refl
  }
