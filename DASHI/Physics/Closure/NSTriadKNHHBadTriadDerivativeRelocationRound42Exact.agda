module DASHI.Physics.Closure.NSTriadKNHHBadTriadDerivativeRelocationRound42Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- Communications on Pure and Applied Mathematics 41 (1988), 891--907.
-- DOI: 10.1002/cpa.3160410704.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Round 41 made the HH-bad inverse-shell route falsifiable: exactly one
-- derivative across a parabolic inverse leaves 2^-q, whereas two genuine
-- derivative-bearing sides are scale-free.  Before counting derivatives in a
-- bounded expression, incompressibility and triad resonance must be exhausted.
--
-- On the literal physical triad p+q=k, divergence freedom gives
--
--   p . u_p = 0,    q . u_q = 0.
--
-- Therefore the apparent output derivative relocates exactly:
--
--   k . u_p = q . u_p,
--   k . u_q = p . u_q.
--
-- This file proves both identities on the repository's actual integer Fourier
-- and Complex3 carriers and constructs them directly from the physical
-- divergence-free velocity state.
--
-- It also proves the crucial diagnostic for the shortest path: if the raw
-- symbol contains *two independent* output contractions, relocation alone does
-- not remove a derivative.  Their product becomes
--
--   (k.u_p)(k.u_q) = (q.u_p)(p.u_q),
--
-- which still has two derivative-bearing factors.  Consequently the desired
-- Round-41 one-derivative factorization must come from the literal structure of
-- the bad gain -- e.g. only one contraction is actually present, or an exact
-- cancellation/defect subtraction removes the other.  Incompressibility by
-- itself cannot be used to smuggle a two-derivative term into the inverse-shell
-- lane.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPhysicalTransportCoefficientSkewRound40Exact as Relocate

record PhysicalTriadDerivativeRelocation
    {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (triad : Physical.PhysicalTriadIncidence) : Set r where
  field
    leftCoefficient rightCoefficient : C3.Complex3 F
    leftDivergenceFree :
      Relocate.modeDot E (Physical.p triad) leftCoefficient
      ≡ C3.complexZero F
    rightDivergenceFree :
      Relocate.modeDot E (Physical.q triad) rightCoefficient
      ≡ C3.complexZero F

open PhysicalTriadDerivativeRelocation public

leftOutputDerivativeRelocatesToRightLeg :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {triad : Physical.PhysicalTriadIncidence} →
  (witness : PhysicalTriadDerivativeRelocation E triad) →
  Relocate.modeDot E (Physical.k triad) (leftCoefficient witness)
  ≡ Relocate.modeDot E (Physical.q triad) (leftCoefficient witness)
leftOutputDerivativeRelocatesToRightLeg {E = E} {triad} witness =
  Relocate.resonantDerivativeRelocation
    E
    (Physical.p triad)
    (Physical.q triad)
    (Physical.k triad)
    (leftCoefficient witness)
    (Physical.resonance triad)
    (leftDivergenceFree witness)

rightOutputDerivativeRelocatesToLeftLeg :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {triad : Physical.PhysicalTriadIncidence} →
  (witness : PhysicalTriadDerivativeRelocation E triad) →
  Relocate.modeDot E (Physical.k triad) (rightCoefficient witness)
  ≡ Relocate.modeDot E (Physical.p triad) (rightCoefficient witness)
rightOutputDerivativeRelocatesToLeftLeg {E = E} {triad} witness =
  Relocate.resonantDerivativeRelocation
    E
    (Physical.q triad)
    (Physical.p triad)
    (Physical.k triad)
    (rightCoefficient witness)
    (trans
      (Symmetry.addModeCommutative (Physical.q triad) (Physical.p triad))
      (Physical.resonance triad))
    (rightDivergenceFree witness)

twoOutputDerivativeProductRelocatesWithoutOrderLoss :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {triad : Physical.PhysicalTriadIncidence} →
  (witness : PhysicalTriadDerivativeRelocation E triad) →
  C3.complexMultiply
    (Relocate.modeDot E (Physical.k triad) (leftCoefficient witness))
    (Relocate.modeDot E (Physical.k triad) (rightCoefficient witness))
  ≡ C3.complexMultiply
      (Relocate.modeDot E (Physical.q triad) (leftCoefficient witness))
      (Relocate.modeDot E (Physical.p triad) (rightCoefficient witness))
twoOutputDerivativeProductRelocatesWithoutOrderLoss witness =
  cong₂ C3.complexMultiply
    (leftOutputDerivativeRelocatesToRightLeg witness)
    (rightOutputDerivativeRelocatesToLeftLeg witness)

physicalVelocityTriadDerivativeRelocation :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.DivergenceFreeCondition E velocity →
  (triad : Physical.PhysicalTriadIncidence) →
  PhysicalTriadDerivativeRelocation E triad
physicalVelocityTriadDerivativeRelocation {E = E}
    velocity divergenceFree triad = record
  { leftCoefficient = velocity (Physical.p triad)
  ; rightCoefficient = velocity (Physical.q triad)
  ; leftDivergenceFree =
      trans
        (Algebra.bilinearDotCommutative
          (C3.modeVector E (Physical.p triad))
          (velocity (Physical.p triad)))
        (divergenceFree (Physical.p triad))
  ; rightDivergenceFree =
      trans
        (Algebra.bilinearDotCommutative
          (C3.modeVector E (Physical.q triad))
          (velocity (Physical.q triad)))
        (divergenceFree (Physical.q triad))
  }

physicalVelocityLeftOutputDerivativeRelocation :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (divergenceFree : Audit.DivergenceFreeCondition E velocity) →
  (triad : Physical.PhysicalTriadIncidence) →
  Relocate.modeDot E (Physical.k triad) (velocity (Physical.p triad))
  ≡ Relocate.modeDot E (Physical.q triad) (velocity (Physical.p triad))
physicalVelocityLeftOutputDerivativeRelocation
    velocity divergenceFree triad =
  leftOutputDerivativeRelocatesToRightLeg
    (physicalVelocityTriadDerivativeRelocation velocity divergenceFree triad)

physicalVelocityRightOutputDerivativeRelocation :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (divergenceFree : Audit.DivergenceFreeCondition E velocity) →
  (triad : Physical.PhysicalTriadIncidence) →
  Relocate.modeDot E (Physical.k triad) (velocity (Physical.q triad))
  ≡ Relocate.modeDot E (Physical.p triad) (velocity (Physical.q triad))
physicalVelocityRightOutputDerivativeRelocation
    velocity divergenceFree triad =
  rightOutputDerivativeRelocatesToLeftLeg
    (physicalVelocityTriadDerivativeRelocation velocity divergenceFree triad)

hhBadTriadDerivativeRelocationClosed : Bool
hhBadTriadDerivativeRelocationClosed = true

physicalHHBadTriadDerivativeRelocationConstructed : Bool
physicalHHBadTriadDerivativeRelocationConstructed = true

twoDerivativeRelocationDoesNotCreateInverseShellGain : Bool
twoDerivativeRelocationDoesNotCreateInverseShellGain = true

physicalHHBadOneDerivativeStillNeedsLiteralSingleFactorOrCancellation : Bool
physicalHHBadOneDerivativeStillNeedsLiteralSingleFactorOrCancellation = true

hhBadTriadDerivativeRelocationClosedIsTrue :
  hhBadTriadDerivativeRelocationClosed ≡ true
hhBadTriadDerivativeRelocationClosedIsTrue = refl

physicalHHBadTriadDerivativeRelocationConstructedIsTrue :
  physicalHHBadTriadDerivativeRelocationConstructed ≡ true
physicalHHBadTriadDerivativeRelocationConstructedIsTrue = refl
