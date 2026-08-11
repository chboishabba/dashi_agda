module DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitFibreRound38Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- AMS Chelsea Publishing, 2001 reprint.
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Advance the remaining F4 multiplicity seam as an orbit-fibre theorem.
-- The two energy-leg maps used by the exact three-leg cancellation are proved
-- involutive on lattice coordinates and proved to preserve the literal cutoff
-- incidence carrier.  Thus every listed physical incidence has listed
-- representatives for both companion energy legs.
--
-- Separately, a proof-relevant finite pushforward theorem shows that summing
-- over a list partition equals summing the fibre folds.  This formulation
-- handles stabilizers by actual fibres rather than by dividing by a formal
-- group order.  What remains open is the concrete partition/equality matching
-- the repository's Galerkin nonlinear-power enumeration to these orbit fibres.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_; _++_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry

pEnergyLegInvolutiveOnLattice :
  ∀ tau →
  Symmetry.SameLatticeTriad
    (Orbit.pEnergyLeg (Orbit.pEnergyLeg tau)) tau
pEnergyLegInvolutiveOnLattice tau =
  Symmetry.same-lattice-triad
    refl
    (Symmetry.negateModeInvolutive (Physical.q tau))
    refl

qEnergyLegInvolutiveOnLattice :
  ∀ tau →
  Symmetry.SameLatticeTriad
    (Orbit.qEnergyLeg (Orbit.qEnergyLeg tau)) tau
qEnergyLegInvolutiveOnLattice tau =
  Symmetry.same-lattice-triad
    refl
    (Symmetry.negateModeInvolutive (Physical.p tau))
    refl

pEnergyLegPreservesCutoff :
  ∀ {cutoff tau} →
  Physical.PhysicalTriadInCutoff cutoff tau →
  Physical.PhysicalTriadInCutoff cutoff (Orbit.pEnergyLeg tau)
pEnergyLegPreservesCutoff {cutoff} {tau} bounded =
  Physical.triad-in-cutoff
    (Physical.kBounded bounded)
    (Cube.cutoffClosedUnderNegation cutoff
      (Physical.q tau)
      (Physical.qBounded bounded))
    (Physical.pBounded bounded)

qEnergyLegPreservesCutoff :
  ∀ {cutoff tau} →
  Physical.PhysicalTriadInCutoff cutoff tau →
  Physical.PhysicalTriadInCutoff cutoff (Orbit.qEnergyLeg tau)
qEnergyLegPreservesCutoff {cutoff} {tau} bounded =
  Physical.triad-in-cutoff
    (Physical.kBounded bounded)
    (Cube.cutoffClosedUnderNegation cutoff
      (Physical.p tau)
      (Physical.pBounded bounded))
    (Physical.qBounded bounded)

enumeratedPEnergyLegHasRepresentative :
  ∀ {cutoff tau} →
  tau Cube.∈ Physical.physicalTriadEnumeration cutoff →
  Physical.PhysicalTriadEnumerationHit
    cutoff (Orbit.pEnergyLeg tau)
enumeratedPEnergyLegHasRepresentative member =
  Physical.physicalTriadEnumerationComplete
    (pEnergyLegPreservesCutoff
      (Physical.physicalTriadEnumerationCutoffSound member))

enumeratedQEnergyLegHasRepresentative :
  ∀ {cutoff tau} →
  tau Cube.∈ Physical.physicalTriadEnumeration cutoff →
  Physical.PhysicalTriadEnumerationHit
    cutoff (Orbit.qEnergyLeg tau)
enumeratedQEnergyLegHasRepresentative member =
  Physical.physicalTriadEnumerationComplete
    (qEnergyLegPreservesCutoff
      (Physical.physicalTriadEnumerationCutoffSound member))

------------------------------------------------------------------------
-- Generic finite fibre pushforward, specialized to rational summands.
------------------------------------------------------------------------

foldRational : ∀ {A : Set} → (A → ℚ) → List A → ℚ
foldRational value [] = 0ℚ
foldRational value (x ∷ xs) = value x + foldRational value xs

foldAppend :
  ∀ {A : Set} (value : A → ℚ) left right →
  foldRational value (left ++ right)
  ≡ foldRational value left + foldRational value right
foldAppend value [] right =
  solve (foldRational value right ∷ [])
foldAppend value (x ∷ xs) right =
  trans
    (cong (value x +_) (foldAppend value xs right))
    (solve
      ( value x
      ∷ foldRational value xs
      ∷ foldRational value right
      ∷ []))

flattenFibres : ∀ {A : Set} → List (List A) → List A
flattenFibres [] = []
flattenFibres (fibre ∷ rest) = fibre ++ flattenFibres rest

foldFibreTotals :
  ∀ {A : Set} → (A → ℚ) → List (List A) → ℚ
foldFibreTotals value [] = 0ℚ
foldFibreTotals value (fibre ∷ rest) =
  foldRational value fibre + foldFibreTotals value rest

finiteFibrePushforward :
  ∀ {A : Set} (value : A → ℚ) fibres →
  foldRational value (flattenFibres fibres)
  ≡ foldFibreTotals value fibres
finiteFibrePushforward value [] = refl
finiteFibrePushforward value (fibre ∷ rest) =
  trans
    (foldAppend value fibre (flattenFibres rest))
    (cong
      (foldRational value fibre +_)
      (finiteFibrePushforward value rest))

record ExactFibrePartition {A : Set} (incidences : List A) : Set₁ where
  field
    fibres : List (List A)
    flattenMeaning : flattenFibres fibres ≡ incidences

open ExactFibrePartition public

pushforwardAlongExactFibrePartition :
  ∀ {A : Set} {incidences : List A} →
  (value : A → ℚ) →
  (partition : ExactFibrePartition incidences) →
  foldRational value incidences
  ≡ foldFibreTotals value (fibres partition)
pushforwardAlongExactFibrePartition value partition =
  trans
    (cong (foldRational value) (sym (flattenMeaning partition)))
    (finiteFibrePushforward value (fibres partition))

physicalTriadOrbitActionOnCutoffClosed : Bool
physicalTriadOrbitActionOnCutoffClosed = true

finiteOrbitFibrePushforwardClosed : Bool
finiteOrbitFibrePushforwardClosed = true

literalGalerkinOrbitFibrePartitionConstructed : Bool
literalGalerkinOrbitFibrePartitionConstructed = false

physicalTriadOrbitActionOnCutoffClosedIsTrue :
  physicalTriadOrbitActionOnCutoffClosed ≡ true
physicalTriadOrbitActionOnCutoffClosedIsTrue = refl

finiteOrbitFibrePushforwardClosedIsTrue :
  finiteOrbitFibrePushforwardClosed ≡ true
finiteOrbitFibrePushforwardClosedIsTrue = refl
