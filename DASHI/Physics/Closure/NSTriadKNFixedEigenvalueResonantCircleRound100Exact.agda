module DASHI.Physics.Closure.NSTriadKNFixedEigenvalueResonantCircleRound100Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Jean Bourgain; Zeev Rudnick.
-- Title: "On the nodal sets of toral eigenfunctions".
-- Inventiones Mathematicae 185 (2011), 199--237.
-- DOI: 10.1007/s00222-010-0307-2.
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- ROUND100 / FIXED-EIGENVALUE RESONANT CIRCLE GEOMETRY
--
-- Refining a periodic Fourier packet by exact Laplacian eigenvalue exposes
-- more arithmetic structure than a dyadic annulus.  For p+q=k, subtraction of
-- the two sphere equations gives the exact affine-plane identity
--
--     2 (p.k) = |p|^2 + |k|^2 - |q|^2.
--
-- Therefore after fixing the three squared radii m=|p|^2, l=|q|^2,
-- n=|k|^2, every admissible p lies on one affine lattice plane.  Combining
-- this with the already-proved Plucker/Gram identity gives the division-free
-- circle invariant
--
--     4 |p x k|^2 = 4 m n - (m+n-l)^2.
--
-- This file proves those exact Z^3 identities.  It does NOT claim a lattice-
-- point cardinality estimate; that arithmetic counting step is the potential
-- analytic gain to exploit next.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; _+_; _-_; _*_)
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadPluckerInvariantRound27Exact as Plane

module RingZ = NR IntRS.ring
open RingZ using (solve)

two four : ℤ
two = + 2
four = + 4

resonantPlaneIdentityForSum :
  ∀ p q →
  two * Plane.dotMode p (Z3.addMode p q)
  ≡ Plane.modeNormSquared p
      + Plane.modeNormSquared (Z3.addMode p q)
      - Plane.modeNormSquared q
resonantPlaneIdentityForSum
    (Z3.mode px py pz) (Z3.mode qx qy qz) =
  RingZ.solve 6
    (λ px py pz qx qy qz →
      ( (+ 2) *
          (px * (px + qx) + py * (py + qy) + pz * (pz + qz))
      , (px * px + py * py + pz * pz)
          + ((px + qx) * (px + qx)
            + (py + qy) * (py + qy)
            + (pz + qz) * (pz + qz))
          - (qx * qx + qy * qy + qz * qz)))
    refl px py pz qx qy qz

resonantPlaneIdentity :
  (tau : Physical.PhysicalTriadIncidence) →
  two * Plane.dotMode (Physical.p tau) (Physical.k tau)
  ≡ Plane.modeNormSquared (Physical.p tau)
      + Plane.modeNormSquared (Physical.k tau)
      - Plane.modeNormSquared (Physical.q tau)
resonantPlaneIdentity tau =
  subst
    (λ output →
      two * Plane.dotMode (Physical.p tau) output
      ≡ Plane.modeNormSquared (Physical.p tau)
          + Plane.modeNormSquared output
          - Plane.modeNormSquared (Physical.q tau))
    (Physical.resonance tau)
    (resonantPlaneIdentityForSum (Physical.p tau) (Physical.q tau))

record FixedTriadEigenvalues
    (tau : Physical.PhysicalTriadIncidence) : Set where
  constructor fixed-triad-eigenvalues
  field
    pEigenvalue qEigenvalue kEigenvalue : ℤ
    pMeaning : Plane.modeNormSquared (Physical.p tau) ≡ pEigenvalue
    qMeaning : Plane.modeNormSquared (Physical.q tau) ≡ qEigenvalue
    kMeaning : Plane.modeNormSquared (Physical.k tau) ≡ kEigenvalue

open FixedTriadEigenvalues public

fixedEigenvaluesForceAffinePlane :
  ∀ {tau} (E : FixedTriadEigenvalues tau) →
  two * Plane.dotMode (Physical.p tau) (Physical.k tau)
  ≡ pEigenvalue E + kEigenvalue E - qEigenvalue E
fixedEigenvaluesForceAffinePlane {tau} E
  rewrite sym (pMeaning E) | sym (qMeaning E) | sym (kMeaning E) =
  resonantPlaneIdentity tau

pluckerWithOutputEqualsInputArea :
  (tau : Physical.PhysicalTriadIncidence) →
  Plane.pluckerNormSquared (Physical.p tau) (Physical.k tau)
  ≡ Plane.pluckerNormSquared (Physical.p tau) (Physical.q tau)
pluckerWithOutputEqualsInputArea tau =
  subst
    (λ output →
      Plane.pluckerNormSquared (Physical.p tau) output
      ≡ Plane.pluckerNormSquared (Physical.p tau) (Physical.q tau))
    (Physical.resonance tau)
    (areaWithSum (Physical.p tau) (Physical.q tau))
  where
  areaWithSum : ∀ p q →
    Plane.pluckerNormSquared p (Z3.addMode p q)
    ≡ Plane.pluckerNormSquared p q
  areaWithSum
      (Z3.mode px py pz) (Z3.mode qx qy qz) =
    RingZ.solve 6
      (λ px py pz qx qy qz →
        ( ((py * (pz + qz) - pz * (py + qy))
            * (py * (pz + qz) - pz * (py + qy))
          + (pz * (px + qx) - px * (pz + qz))
            * (pz * (px + qx) - px * (pz + qz)))
          + (px * (py + qy) - py * (px + qx))
            * (px * (py + qy) - py * (px + qx))
        , ((py * qz - pz * qy) * (py * qz - pz * qy)
          + (pz * qx - px * qz) * (pz * qx - px * qz))
          + (px * qy - py * qx) * (px * qy - py * qx)))
      refl px py pz qx qy qz

fixedEigenvalueCircleInvariant :
  ∀ {tau} (E : FixedTriadEigenvalues tau) →
  four * Plane.pluckerNormSquared (Physical.p tau) (Physical.k tau)
  ≡ four * (pEigenvalue E * kEigenvalue E)
      - (pEigenvalue E + kEigenvalue E - qEigenvalue E)
        * (pEigenvalue E + kEigenvalue E - qEigenvalue E)
fixedEigenvalueCircleInvariant {tau} E =
  let
    gram = Plane.pluckerGramIdentity (Physical.p tau) (Physical.k tau)
    plane = fixedEigenvaluesForceAffinePlane E
  in
  subst
    (λ pNorm →
      four * Plane.pluckerNormSquared (Physical.p tau) (Physical.k tau)
      ≡ four * (pNorm * kEigenvalue E)
        - (pNorm + kEigenvalue E - qEigenvalue E)
          * (pNorm + kEigenvalue E - qEigenvalue E))
    (pMeaning E)
    (subst
      (λ kNorm →
        four * Plane.pluckerNormSquared (Physical.p tau) (Physical.k tau)
        ≡ four * (Plane.modeNormSquared (Physical.p tau) * kNorm)
          - (Plane.modeNormSquared (Physical.p tau) + kNorm - qEigenvalue E)
            * (Plane.modeNormSquared (Physical.p tau) + kNorm - qEigenvalue E))
      (kMeaning E)
      (subst
        (λ qNorm →
          four * Plane.pluckerNormSquared (Physical.p tau) (Physical.k tau)
          ≡ four *
              (Plane.modeNormSquared (Physical.p tau)
                * Plane.modeNormSquared (Physical.k tau))
            - (Plane.modeNormSquared (Physical.p tau)
                + Plane.modeNormSquared (Physical.k tau) - qNorm)
              * (Plane.modeNormSquared (Physical.p tau)
                + Plane.modeNormSquared (Physical.k tau) - qNorm))
        (qMeaning E)
        (circleFromGramAndPlane tau gram (resonantPlaneIdentity tau))))
  where
  circleFromGramAndPlane :
    (tau : Physical.PhysicalTriadIncidence) →
    Plane.pluckerNormSquared (Physical.p tau) (Physical.k tau)
      ≡ Plane.modeNormSquared (Physical.p tau)
        * Plane.modeNormSquared (Physical.k tau)
        - Plane.dotMode (Physical.p tau) (Physical.k tau)
          * Plane.dotMode (Physical.p tau) (Physical.k tau) →
    two * Plane.dotMode (Physical.p tau) (Physical.k tau)
      ≡ Plane.modeNormSquared (Physical.p tau)
        + Plane.modeNormSquared (Physical.k tau)
        - Plane.modeNormSquared (Physical.q tau) →
    four * Plane.pluckerNormSquared (Physical.p tau) (Physical.k tau)
      ≡ four *
          (Plane.modeNormSquared (Physical.p tau)
            * Plane.modeNormSquared (Physical.k tau))
        - (Plane.modeNormSquared (Physical.p tau)
            + Plane.modeNormSquared (Physical.k tau)
            - Plane.modeNormSquared (Physical.q tau))
          * (Plane.modeNormSquared (Physical.p tau)
            + Plane.modeNormSquared (Physical.k tau)
            - Plane.modeNormSquared (Physical.q tau))
  circleFromGramAndPlane tau gram plane
    rewrite gram | sym plane = RingZ.solve 1
      (λ d →
        ( (+ 4) *
            ((Plane.modeNormSquared (Physical.p tau)
              * Plane.modeNormSquared (Physical.k tau)) - d * d)
        , (+ 4) *
            (Plane.modeNormSquared (Physical.p tau)
              * Plane.modeNormSquared (Physical.k tau))
          - ((+ 2) * d) * ((+ 2) * d)))
      refl (Plane.dotMode (Physical.p tau) (Physical.k tau))

round100FixedEigenvalueResonanceLiesOnAffineLatticePlane : Bool
round100FixedEigenvalueResonanceLiesOnAffineLatticePlane = true

round100FixedEigenvalueResonanceHasDivisionFreeCircleInvariant : Bool
round100FixedEigenvalueResonanceHasDivisionFreeCircleInvariant = true

round100FixedEigenvalueResonanceHasDivisionFreeCircleInvariantIsTrue :
  round100FixedEigenvalueResonanceHasDivisionFreeCircleInvariant ≡ true
round100FixedEigenvalueResonanceHasDivisionFreeCircleInvariantIsTrue = refl
