module DASHI.Physics.Closure.NSTriadKNWeakTypeVolumeStarvationNoGoExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Alberto P. Calderón; Antoni Zygmund.
-- Mathematical ingredient: weak-type (1,1) distribution estimates for
-- singular integral operators.
-- DOI: not assigned here; this module proves a repository-original finite
-- counterexample to an invalid inference from weak-type control to L-infinity
-- control.
--
-- Authors: J. Thomas Beale; Tosio Kato; Andrew Majda.
-- Title: "Remarks on the Breakdown of Smooth Solutions for the 3-D Euler
-- Equations".
-- Communications in Mathematical Physics 94 (1984), 61--66.
-- DOI: 10.1007/BF01240221.
--
-- PURPOSE
-- Audit the proposed "volume starvation prevents blowup" step.  A dyadic
-- spike can have amplitude lambda_q and support measure lambda_q^{-1}.  Its
-- L1 mass and weak-type product are exactly one at every scale, while its
-- amplitude doubles without bound along the finite shell sequence:
--
--   amplitude_q * measure_q = 1,
--   amplitude_{q+1} = 2 amplitude_q.
--
-- Thus weak-(1,1) control is compatible with increasingly tall spikes on
-- increasingly small sets.  It is useful partial information, but it cannot
-- by itself imply the BKM L-infinity time integral is finite.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteEnergyCriticalScalingGapExact as Scale
import DASHI.Physics.Closure.NSTriadKNLuoFiniteNearWindowHalfKernelExact as Near
import DASHI.Physics.Closure.NSTriadKNLuoFiniteNearWindowScalingObstructionExact as Reciprocal

spikeAmplitude : Nat → ℚ
spikeAmplitude = Scale.dyadicScale

spikeSupportMeasure : Nat → ℚ
spikeSupportMeasure = Near.windowRoot

weakTypeProduct : Nat → ℚ
weakTypeProduct shell =
  spikeAmplitude shell * spikeSupportMeasure shell

weakTypeProductIsOne :
  (shell : Nat) →
  weakTypeProduct shell ≡ 1ℚ
weakTypeProductIsOne shell =
  trans
    (solve
      ( Scale.dyadicScale shell
      ∷ Near.windowRoot shell
      ∷ []))
    (Reciprocal.reciprocalDyadicIdentity shell)

spikeAmplitudeDoubles :
  (shell : Nat) →
  spikeAmplitude (suc shell)
  ≡ Scale.two * spikeAmplitude shell
spikeAmplitudeDoubles = Scale.dyadicScaleSuccessor

spikeSupportHalves :
  (shell : Nat) →
  spikeSupportMeasure (suc shell)
  ≡ Near.half * spikeSupportMeasure shell
spikeSupportHalves = Near.windowRootHalves

massPreservedAcrossConcentration :
  (shell : Nat) →
  weakTypeProduct (suc shell) ≡ weakTypeProduct shell
massPreservedAcrossConcentration shell =
  trans
    (weakTypeProductIsOne (suc shell))
    (sym (weakTypeProductIsOne shell))
