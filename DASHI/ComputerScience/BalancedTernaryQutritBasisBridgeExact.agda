module DASHI.ComputerScience.BalancedTernaryQutritBasisBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Algebra.Quantum.FiniteQutrit as Qutrit
import DASHI.Algebra.Quantum.QutritWeyl as Weyl

------------------------------------------------------------------------
-- BALANCED C3 <-> QUTRIT COMPUTATIONAL BASIS
--
-- This is a basis-label equivalence only.  It does not identify a classical
-- balanced-trit cell with a general quantum qutrit state or superposition.
-- The chosen labelling is the canonical signed mod-3 one:
--
--   0  -> |0>
--   +1 -> |1>
--   -1 -> |2>    because -1 = 2 mod 3.
--
-- Under this labelling the cyclic C3 successor intertwines exactly with the
-- qutrit Weyl X shift.
------------------------------------------------------------------------

tritToQutritBasis : SSP.SSPTrit → Qutrit.QutritBasis
tritToQutritBasis SSP.sspZero = Qutrit.ket0
tritToQutritBasis SSP.sspPosOne = Qutrit.ket1
tritToQutritBasis SSP.sspNegOne = Qutrit.ket2

qutritBasisToTrit : Qutrit.QutritBasis → SSP.SSPTrit
qutritBasisToTrit Qutrit.ket0 = SSP.sspZero
qutritBasisToTrit Qutrit.ket1 = SSP.sspPosOne
qutritBasisToTrit Qutrit.ket2 = SSP.sspNegOne

qutritAfterTritRoundTrip :
  (t : SSP.SSPTrit) →
  qutritBasisToTrit (tritToQutritBasis t) ≡ t
qutritAfterTritRoundTrip SSP.sspNegOne = refl
qutritAfterTritRoundTrip SSP.sspZero = refl
qutritAfterTritRoundTrip SSP.sspPosOne = refl

tritAfterQutritRoundTrip :
  (q : Qutrit.QutritBasis) →
  tritToQutritBasis (qutritBasisToTrit q) ≡ q
tritAfterQutritRoundTrip Qutrit.ket0 = refl
tritAfterQutritRoundTrip Qutrit.ket1 = refl
tritAfterQutritRoundTrip Qutrit.ket2 = refl

cycleC3 : SSP.SSPTrit → SSP.SSPTrit
cycleC3 SSP.sspZero = SSP.sspPosOne
cycleC3 SSP.sspPosOne = SSP.sspNegOne
cycleC3 SSP.sspNegOne = SSP.sspZero

cycleC3OrderThree :
  (t : SSP.SSPTrit) →
  cycleC3 (cycleC3 (cycleC3 t)) ≡ t
cycleC3OrderThree SSP.sspNegOne = refl
cycleC3OrderThree SSP.sspZero = refl
cycleC3OrderThree SSP.sspPosOne = refl

weylXIntertwinesC3Cycle :
  (t : SSP.SSPTrit) →
  tritToQutritBasis (cycleC3 t) ≡ Weyl.X (tritToQutritBasis t)
weylXIntertwinesC3Cycle SSP.sspNegOne = refl
weylXIntertwinesC3Cycle SSP.sspZero = refl
weylXIntertwinesC3Cycle SSP.sspPosOne = refl

record BalancedTernaryQutritBasisBoundary : Set where
  constructor balancedTernaryQutritBasisBoundary
  field
    basisLabelsRoundTripExactly : Bool
    c3CycleIntertwinesWeylShift : Bool
    classicalTritEqualsGeneralQuantumState : Bool
    basisEquivalenceProvesSuperpositionEquivalence : Bool
    antipodeEqualsWeylShift : Bool
    quantumPhaseAlreadyClassicalTritData : Bool

canonicalBalancedTernaryQutritBasisBoundary :
  BalancedTernaryQutritBasisBoundary
canonicalBalancedTernaryQutritBasisBoundary =
  balancedTernaryQutritBasisBoundary
    true true false false false false
