module DASHI.Physics.Closure.NSTriadKNComBonyBranchGeometryRound66Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND 66 / B3 PHYSICAL BRANCH GEOMETRY
--
-- For the literal transport entry attached to p+q=k, p is the advector, q is
-- the differentiated input and k is the output.  Round66's dominant-low split
-- therefore has a direct Bony interpretation:
--
--   lowP : low advector / two dominant q,k endpoints,
--   lowQ : low differentiated input / dominant p,k,
--   lowK : low output / dominant p,q.
--
-- In the low-advector branch the incompressibility identity also relocates the
-- derivative EXACTLY between the two dominant endpoints:
--
--   k . u_p = q . u_p.
--
-- This is the literal Fourier identity needed before estimating the Taylor
-- multiplier difference.  The theorem below packages the branch geometry and
-- this exact derivative relocation on the same PhysicalTriadIncidence.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNOfficialInfinityNormTriangle as Infinity
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNComDyadicHatWidthOneRound46Exact as Width
import DASHI.Physics.Closure.NSTriadKNPhysicalTransportCoefficientSkewRound40Exact as Transport
import DASHI.Physics.Closure.NSTriadKNResonantDominantLowLegSplitRound66Exact as Split

literalTriadDerivativeRelocation :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.DivergenceFreeCondition E velocity →
  (tau : Physical.PhysicalTriadIncidence) →
  Transport.modeDot E (Physical.k tau) (velocity (Physical.p tau))
  ≡ Transport.modeDot E (Physical.q tau) (velocity (Physical.p tau))
literalTriadDerivativeRelocation E velocity divergenceFree tau =
  Transport.resonantDerivativeRelocation
    E
    (Physical.p tau)
    (Physical.q tau)
    (Physical.k tau)
    (velocity (Physical.p tau))
    (Physical.resonance tau)
    (trans
      (Algebra.bilinearDotCommutative
        (C3.modeVector E (Physical.p tau))
        (velocity (Physical.p tau)))
      (divergenceFree (Physical.p tau)))

data PhysicalComBonyBranch
    {r : Level}
    {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (tau : Physical.PhysicalTriadIncidence) : Set r where

  lowAdvector :
    Infinity.infinityNorm (Physical.p tau)
      ≤ Infinity.infinityNorm (Physical.q tau) →
    Infinity.infinityNorm (Physical.p tau)
      ≤ Infinity.infinityNorm (Physical.k tau) →
    Width.WithinOne
      (Shell.shellIndex (Physical.q tau))
      (Shell.shellIndex (Physical.k tau)) →
    Transport.modeDot E (Physical.k tau) (velocity (Physical.p tau))
      ≡ Transport.modeDot E (Physical.q tau) (velocity (Physical.p tau)) →
    PhysicalComBonyBranch E velocity tau

  lowInput :
    Infinity.infinityNorm (Physical.q tau)
      ≤ Infinity.infinityNorm (Physical.p tau) →
    Infinity.infinityNorm (Physical.q tau)
      ≤ Infinity.infinityNorm (Physical.k tau) →
    Width.WithinOne
      (Shell.shellIndex (Physical.p tau))
      (Shell.shellIndex (Physical.k tau)) →
    PhysicalComBonyBranch E velocity tau

  lowOutput :
    Infinity.infinityNorm (Physical.k tau)
      ≤ Infinity.infinityNorm (Physical.p tau) →
    Infinity.infinityNorm (Physical.k tau)
      ≤ Infinity.infinityNorm (Physical.q tau) →
    Width.WithinOne
      (Shell.shellIndex (Physical.p tau))
      (Shell.shellIndex (Physical.q tau)) →
    PhysicalComBonyBranch E velocity tau

literalPhysicalComBonyBranch :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.DivergenceFreeCondition E velocity →
  (tau : Physical.PhysicalTriadIncidence) →
  PhysicalComBonyBranch E velocity tau
literalPhysicalComBonyBranch E velocity divergenceFree tau
  with Split.resonantDominantLowLegSplit tau
... | Split.lowP p≤q p≤k qkWithin =
      lowAdvector p≤q p≤k qkWithin
        (literalTriadDerivativeRelocation E velocity divergenceFree tau)
... | Split.lowQ q≤p q≤k pkWithin =
      lowInput q≤p q≤k pkWithin
... | Split.lowK k≤p k≤q pqWithin =
      lowOutput k≤p k≤q pqWithin

round66LiteralComBonyBranchConstructed : Bool
round66LiteralComBonyBranchConstructed = true

round66LowAdvectorDerivativeRelocationConstructed : Bool
round66LowAdvectorDerivativeRelocationConstructed = true

round66LiteralComBonyBranchConstructedIsTrue :
  round66LiteralComBonyBranchConstructed ≡ true
round66LiteralComBonyBranchConstructedIsTrue = refl

round66LowAdvectorDerivativeRelocationConstructedIsTrue :
  round66LowAdvectorDerivativeRelocationConstructed ≡ true
round66LowAdvectorDerivativeRelocationConstructedIsTrue = refl
