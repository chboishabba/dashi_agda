module DASHI.Physics.Closure.NSTriadKNLiteralBoundaryTriadsInstantiateBonyChannelsRound97Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "The Regularity of Weak Solutions of the 3D Navier-Stokes
-- Equations in B^{-1}_{infinity,infinity}".
-- Archive for Rational Mechanics and Analysis 195 (2010), 159--169.
-- DOI: 10.1007/s00205-009-0265-2.
--
-- ROUND97 / SAME-OBJECT BOUNDARY-TO-BONY ADAPTER
--
-- Round96 proved that packet energy transfer may be reduced exactly to
-- boundary-crossing physical triads before positive taxation.  The repository
-- already owns an executable Bony classifier on `ConcreteNearTriad`.  This
-- file proves that every literal `PhysicalTriadIncidence` maps to that carrier
-- without changing p, q, k, or the resonance equation, and hence every
-- packet-boundary physical triad receives exactly one computed near-channel
-- tag (low-high, high-low, or high-high).
--
-- No coefficient estimate is asserted here: this is the exact carrier weld
-- needed before the Round91/official multiplicity machinery is applied.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSPeriodicConcreteNearTriadSums as Near
import DASHI.Physics.Closure.NSPeriodicNearTriadClassification as Classify
import DASHI.Physics.Closure.NSPeriodicFiniteTriadPartition as Partition

physicalAsConcreteNearTriad :
  Physical.PhysicalTriadIncidence → Near.ConcreteNearTriad
physicalAsConcreteNearTriad tau = Near.triad
  (Physical.p tau)
  (Physical.q tau)
  (Physical.k tau)
  (Physical.resonance tau)

physicalPIsPreserved : ∀ tau →
  Near.p (physicalAsConcreteNearTriad tau) ≡ Physical.p tau
physicalPIsPreserved tau = refl

physicalQIsPreserved : ∀ tau →
  Near.q (physicalAsConcreteNearTriad tau) ≡ Physical.q tau
physicalQIsPreserved tau = refl

physicalKIsPreserved : ∀ tau →
  Near.k (physicalAsConcreteNearTriad tau) ≡ Physical.k tau
physicalKIsPreserved tau = refl

physicalResonanceIsPreserved : ∀ tau →
  Near.resonance (physicalAsConcreteNearTriad tau)
  ≡ Physical.resonance tau
physicalResonanceIsPreserved tau = refl

physicalBonyClass :
  Classify.NearShellPolicy →
  Physical.PhysicalTriadIncidence →
  Partition.NearClass
physicalBonyClass policy tau =
  Classify.classifyTriad policy (physicalAsConcreteNearTriad tau)

record LiteralPhysicalBonyChannel
    (policy : Classify.NearShellPolicy)
    (tau : Physical.PhysicalTriadIncidence) : Set where
  constructor literal-physical-bony-channel
  field
    concreteTriad : Near.ConcreteNearTriad
    sameP : Near.p concreteTriad ≡ Physical.p tau
    sameQ : Near.q concreteTriad ≡ Physical.q tau
    sameK : Near.k concreteTriad ≡ Physical.k tau
    channel : Partition.NearClass
    channelIsComputed :
      channel ≡ Classify.classifyTriad policy concreteTriad

open LiteralPhysicalBonyChannel public

literalPhysicalTriadHasUniqueComputedBonyChannel :
  (policy : Classify.NearShellPolicy) →
  (tau : Physical.PhysicalTriadIncidence) →
  LiteralPhysicalBonyChannel policy tau
literalPhysicalTriadHasUniqueComputedBonyChannel policy tau = record
  { concreteTriad = physicalAsConcreteNearTriad tau
  ; sameP = refl
  ; sameQ = refl
  ; sameK = refl
  ; channel = physicalBonyClass policy tau
  ; channelIsComputed = refl
  }

-- A packet-boundary triad is still the same physical incidence; boundary
-- status is deliberately an extra predicate, not a replacement carrier.
record BoundaryPhysicalTriad
    (selected : Z3.FourierMode → Bool) : Set where
  constructor boundary-physical-triad
  field
    incidence : Physical.PhysicalTriadIncidence
    crossesBoundary : Set

open BoundaryPhysicalTriad public

literalBoundaryTriadHasComputedBonyChannel :
  (policy : Classify.NearShellPolicy) →
  {selected : Z3.FourierMode → Bool} →
  (bt : BoundaryPhysicalTriad selected) →
  LiteralPhysicalBonyChannel policy (incidence bt)
literalBoundaryTriadHasComputedBonyChannel policy bt =
  literalPhysicalTriadHasUniqueComputedBonyChannel policy (incidence bt)

round97LiteralBoundaryTriadsInstantiateBonyChannels : Bool
round97LiteralBoundaryTriadsInstantiateBonyChannels = true

round97LiteralBoundaryTriadsInstantiateBonyChannelsIsTrue :
  round97LiteralBoundaryTriadsInstantiateBonyChannels ≡ true
round97LiteralBoundaryTriadsInstantiateBonyChannelsIsTrue = refl
