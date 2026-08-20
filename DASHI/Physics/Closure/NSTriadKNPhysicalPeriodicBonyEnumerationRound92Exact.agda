module DASHI.Physics.Closure.NSTriadKNPhysicalPeriodicBonyEnumerationRound92Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- Annales scientifiques de l'Ecole Normale Superieure 14 (1981).
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- ROUND92 / LITERAL ENUMERATION ADAPTER
--
-- The repository already has:
--
--   * a duplicate-free complete finite enumeration of literal resonant Fourier
--     triads in the cutoff cube; and
--   * an exact six-way periodic Bony/Tao classification of a resonant triad
--     interaction, with decomposition followed by erasure equal to identity.
--
-- This file joins those carriers rather than re-enumerating anything.  A
-- caller supplies the ACTUAL coefficient attached to each physical incidence;
-- `decoratePhysicalTriad` retains p,q,k and its exact resonance and adds only
-- that coefficient.  Forgetting the decoration returns the same physical triad
-- definitionally.  Mapping over the literal cutoff enumeration and then Bony-
-- classifying it is therefore an exhaustive classification of exactly those
-- physical incidences, not a synthetic shell list.
--
-- This closes the enumeration/classification half of the Round91 periodic
-- nonlinear-ledger seam.  It deliberately does not claim the remaining
-- coefficient-to-cubic-L3 charge estimate.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_; map)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as Bony
import DASHI.Physics.Closure.NSTriadKNExactDyadicShellGeometry as Geometry
import DASHI.Physics.Closure.NSTriadKNTaoFrozenLegParaproductProgram as Tao

physicalResonanceToBonyResonance :
  (tau : Physical.PhysicalTriadIncidence) →
  Z3.Resonance (Physical.p tau) (Physical.q tau) (Physical.k tau)
physicalResonanceToBonyResonance tau =
  record { closes = Physical.resonance tau }

decoratePhysicalTriad :
  ∀ {r : Level}
    {model : Bony.PeriodicHardShellFourierPDE {r}} →
  (Physical.PhysicalTriadIncidence → C3.Complex3 (Bony.realField model)) →
  Physical.PhysicalTriadIncidence →
  Bony.PeriodicTriadInteraction model
decoratePhysicalTriad coefficientOf tau =
  Bony.interaction
    (Physical.p tau)
    (Physical.q tau)
    (Physical.k tau)
    (physicalResonanceToBonyResonance tau)
    (coefficientOf tau)

forgetPeriodicTriad :
  ∀ {r : Level}
    {model : Bony.PeriodicHardShellFourierPDE {r}} →
  Bony.PeriodicTriadInteraction model →
  Physical.PhysicalTriadIncidence
forgetPeriodicTriad triad =
  Physical.physicalTriad
    (Bony.leftMode triad)
    (Bony.rightMode triad)
    (Bony.outputMode triad)
    (Z3.Resonance.closes (Bony.resonance triad))

forgetDecoratedPhysicalTriad :
  ∀ {r : Level}
    {model : Bony.PeriodicHardShellFourierPDE {r}}
    (coefficientOf :
      Physical.PhysicalTriadIncidence → C3.Complex3 (Bony.realField model))
    (tau : Physical.PhysicalTriadIncidence) →
  forgetPeriodicTriad (decoratePhysicalTriad coefficientOf tau) ≡ tau
forgetDecoratedPhysicalTriad coefficientOf
  (Physical.physicalTriad p q k resonance) = refl

decoratedPhysicalEnumeration :
  ∀ {r : Level}
    {model : Bony.PeriodicHardShellFourierPDE {r}} →
  (Physical.PhysicalTriadIncidence → C3.Complex3 (Bony.realField model)) →
  Nat → List (Bony.PeriodicTriadInteraction model)
decoratedPhysicalEnumeration coefficientOf cutoff =
  map (decoratePhysicalTriad coefficientOf)
    (Physical.physicalTriadEnumeration cutoff)

forgetPeriodicTriads :
  ∀ {r : Level}
    {model : Bony.PeriodicHardShellFourierPDE {r}} →
  List (Bony.PeriodicTriadInteraction model) →
  List Physical.PhysicalTriadIncidence
forgetPeriodicTriads = map forgetPeriodicTriad

forgetDecoratedPhysicalEnumeration :
  ∀ {r : Level}
    {model : Bony.PeriodicHardShellFourierPDE {r}}
    (coefficientOf :
      Physical.PhysicalTriadIncidence → C3.Complex3 (Bony.realField model))
    (cutoff : Nat) →
  forgetPeriodicTriads (decoratedPhysicalEnumeration coefficientOf cutoff)
    ≡ Physical.physicalTriadEnumeration cutoff
forgetDecoratedPhysicalEnumeration coefficientOf cutoff =
  go (Physical.physicalTriadEnumeration cutoff)
  where
  go :
    (triads : List Physical.PhysicalTriadIncidence) →
    map forgetPeriodicTriad (map (decoratePhysicalTriad coefficientOf) triads)
      ≡ triads
  go [] = refl
  go (tau ∷ rest)
    rewrite forgetDecoratedPhysicalTriad coefficientOf tau
          | go rest = refl

classifiedPhysicalEnumeration :
  ∀ {r : Level}
    {model : Bony.PeriodicHardShellFourierPDE {r}} →
  Geometry.CanonicalGeometryPartition →
  Tao.FrozenLeg →
  (Physical.PhysicalTriadIncidence → C3.Complex3 (Bony.realField model)) →
  Nat → List (Bony.ClassifiedPeriodicInteraction {model = model})
classifiedPhysicalEnumeration partition frozen coefficientOf cutoff =
  Bony.decomposeInteractions partition frozen
    (decoratedPhysicalEnumeration coefficientOf cutoff)

eraseClassifiedPhysicalEnumeration :
  ∀ {r : Level}
    {model : Bony.PeriodicHardShellFourierPDE {r}}
    (partition : Geometry.CanonicalGeometryPartition)
    (frozen : Tao.FrozenLeg)
    (coefficientOf :
      Physical.PhysicalTriadIncidence → C3.Complex3 (Bony.realField model))
    (cutoff : Nat) →
  Bony.eraseInteractions
    (classifiedPhysicalEnumeration partition frozen coefficientOf cutoff)
  ≡ decoratedPhysicalEnumeration coefficientOf cutoff
eraseClassifiedPhysicalEnumeration partition frozen coefficientOf cutoff =
  Bony.eraseDecomposedInteractions partition frozen
    (decoratedPhysicalEnumeration coefficientOf cutoff)

round92LiteralPhysicalTriadEnumerationDecoratedIntoBonyCarrier : Bool
round92LiteralPhysicalTriadEnumerationDecoratedIntoBonyCarrier = true

round92LiteralPhysicalBonyClassificationExhaustive : Bool
round92LiteralPhysicalBonyClassificationExhaustive = true

round92PhysicalCoefficientToCubicChargeBoundConstructed : Bool
round92PhysicalCoefficientToCubicChargeBoundConstructed = false

round92LiteralPhysicalTriadEnumerationDecoratedIntoBonyCarrierIsTrue :
  round92LiteralPhysicalTriadEnumerationDecoratedIntoBonyCarrier ≡ true
round92LiteralPhysicalTriadEnumerationDecoratedIntoBonyCarrierIsTrue = refl

round92LiteralPhysicalBonyClassificationExhaustiveIsTrue :
  round92LiteralPhysicalBonyClassificationExhaustive ≡ true
round92LiteralPhysicalBonyClassificationExhaustiveIsTrue = refl
