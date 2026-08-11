module DASHI.Physics.Closure.NSTriadKNRationalPhysicalTriadEnergyRound37Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- The Round-30 finite-energy interface still marks its canonical orbit
-- producer as open, but the repository has since proved substantially more
-- concrete mathematics: literal cutoff triad enumeration plus exact C^3
-- three-leg cancellation from resonance, Fourier reality and transversality.
--
-- This module connects those developments on the exact rational carrier.
-- For every physical triad incidence tau define the literal three-leg power as
-- the real coordinate of the already-proved ordered-pair transfer sum over
-- tau, its p-energy leg and its q-energy leg.  The concrete C^3 theorem gives
--
--   threeLegPower(tau) = 0
--
-- for every reality-compatible divergence-free state.  Folding this power
-- over the *literal duplicate-free cutoff enumeration* therefore gives zero
-- exactly.
--
-- This closes a genuine F4 algebraic subgate without inventing a packet or a
-- caller-supplied cancellation witness.  What still remains for the global
-- finite-energy identity is the same-object equality identifying the complete
-- Galerkin nonlinear power with this enumerated three-leg fold, including its
-- orbit multiplicity convention.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3EnergyCancellation as Energy

F : C3.RealField _
F = Rational.rationalRealField

threeLegComplexPower :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  Physical.PhysicalTriadIncidence →
  (Z3.FourierMode → C3.Complex3 F) →
  C3.Complex F
threeLegComplexPower E I tau velocity =
  C3.complexAdd
    (C3.complexAdd
      (Audit.orderedPairSignedTransferAt E I tau velocity)
      (Audit.orderedPairSignedTransferAt E I
        (Orbit.pEnergyLeg tau) velocity))
    (Audit.orderedPairSignedTransferAt E I
      (Orbit.qEnergyLeg tau) velocity)

literalThreeLegPower :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  Physical.PhysicalTriadIncidence →
  (Z3.FourierMode → C3.Complex3 F) → ℚ
literalThreeLegPower E I tau velocity =
  C3.real (threeLegComplexPower E I tau velocity)

literalPhysicalTriadPowerZero :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (tau : Physical.PhysicalTriadIncidence) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition velocity →
  Audit.DivergenceFreeCondition E velocity →
  literalThreeLegPower E I tau velocity ≡ 0ℚ
literalPhysicalTriadPowerZero E I tau velocity reality divergenceFree =
  cong C3.real
    (Audit.completeTriadCancellation
      (Energy.exactTriadEnergyCancellation E I tau)
      velocity reality divergenceFree)

sumLiteralTriadPower :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence → ℚ
sumLiteralTriadPower E I velocity [] = 0ℚ
sumLiteralTriadPower E I velocity (tau ∷ rest) =
  literalThreeLegPower E I tau velocity
  + sumLiteralTriadPower E I velocity rest

allPhysicalTriadPowersZero :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition velocity →
  Audit.DivergenceFreeCondition E velocity →
  (triads : List Physical.PhysicalTriadIncidence) →
  sumLiteralTriadPower E I velocity triads ≡ 0ℚ
allPhysicalTriadPowersZero E I velocity reality divergenceFree [] = refl
allPhysicalTriadPowersZero E I velocity reality divergenceFree (tau ∷ rest) =
  trans
    (cong
      (literalThreeLegPower E I tau velocity +_)
      (allPhysicalTriadPowersZero
        E I velocity reality divergenceFree rest))
    (trans
      (cong (_+ 0ℚ)
        (literalPhysicalTriadPowerZero
          E I tau velocity reality divergenceFree))
      (solve []))

literalCutoffTriadPowerSumZero :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (cutoff : Nat) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition velocity →
  Audit.DivergenceFreeCondition E velocity →
  sumLiteralTriadPower E I velocity
    (Physical.physicalTriadEnumeration cutoff)
  ≡ 0ℚ
literalCutoffTriadPowerSumZero E I cutoff velocity reality divergenceFree =
  allPhysicalTriadPowersZero
    E I velocity reality divergenceFree
    (Physical.physicalTriadEnumeration cutoff)

literalCutoffTriadEnumerationDuplicateFree :
  ∀ cutoff →
  Cube.NoDuplicates (Physical.physicalTriadEnumeration cutoff)
literalCutoffTriadEnumerationDuplicateFree =
  Physical.physicalTriadEnumerationNoDuplicates

rationalPhysicalTriadEnergyCancellationClosed : Bool
rationalPhysicalTriadEnergyCancellationClosed = true

literalGalerkinPowerEqualsEnumeratedTriadFoldConstructed : Bool
literalGalerkinPowerEqualsEnumeratedTriadFoldConstructed = false

rationalPhysicalTriadEnergyCancellationClosedIsTrue :
  rationalPhysicalTriadEnergyCancellationClosed ≡ true
rationalPhysicalTriadEnergyCancellationClosedIsTrue = refl

literalGalerkinPowerEqualsEnumeratedTriadFoldConstructedIsFalse :
  literalGalerkinPowerEqualsEnumeratedTriadFoldConstructed ≡ false
literalGalerkinPowerEqualsEnumeratedTriadFoldConstructedIsFalse = refl
