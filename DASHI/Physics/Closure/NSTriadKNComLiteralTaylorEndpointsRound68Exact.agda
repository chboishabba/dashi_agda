module DASHI.Physics.Closure.NSTriadKNComLiteralTaylorEndpointsRound68Exact where

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
-- ROUND 68 / LITERAL TAYLOR ENDPOINTS
--
-- Round66 identified the low leg in every exact resonance p+q=k.  This file
-- now makes the displacement used by the multiplier Taylor theorem literally
-- that low leg, branch by branch:
--
--   low advector: q + p = k,
--   low input:    p + q = k,
--   low output:  (-q) + k = p.
--
-- The last orientation uses Round67's evenness S(-q)=S(q): its two dominant
-- physical multipliers can be compared at -q and p while the displacement is
-- exactly the low output k.  No "comparable endpoints" existential remains
-- between the Round66 branch split and the Taylor variable.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_; _+_; -_)
import Data.Integer.Properties as ℤP
open import Data.Nat.Base using (_≤_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; module ≡-Reasoning)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNOfficialInfinityNormTriangle as Infinity
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNComDyadicHatWidthOneRound46Exact as Width
import DASHI.Physics.Closure.NSTriadKNResonantDominantLowLegSplitRound66Exact as Split

modeExt : ∀ {a b : Z3.FourierMode} →
  Z3.kx a ≡ Z3.kx b →
  Z3.ky a ≡ Z3.ky b →
  Z3.kz a ≡ Z3.kz b →
  a ≡ b
modeExt {Z3.mode ax ay az} {Z3.mode .ax .ay .az} refl refl refl = refl

modeAddCommutative : ∀ a b →
  Z3.addMode a b ≡ Z3.addMode b a
modeAddCommutative (Z3.mode ax ay az) (Z3.mode bx by bz) =
  modeExt
    (ℤP.+-comm ax bx)
    (ℤP.+-comm ay by)
    (ℤP.+-comm az bz)

negatedLeftCancellationScalar : ∀ a b →
  (- b) + (a + b) ≡ a
negatedLeftCancellationScalar a b =
  begin
    (- b) + (a + b)
  ≡⟨ sym (ℤP.+-assoc (- b) a b) ⟩
    ((- b) + a) + b
  ≡⟨ cong (_+ b) (ℤP.+-comm (- b) a) ⟩
    (a + (- b)) + b
  ≡⟨ ℤP.+-assoc a (- b) b ⟩
    a + ((- b) + b)
  ≡⟨ cong (a +_) (ℤP.+-inverseˡ b) ⟩
    a + (+ 0)
  ≡⟨ ℤP.+-identityʳ a ⟩
    a
  ∎
  where open ≡-Reasoning

negatedLeftModeCancellation : ∀ p q →
  Z3.addMode (Z3.negateMode q) (Z3.addMode p q) ≡ p
negatedLeftModeCancellation
    (Z3.mode px py pz) (Z3.mode qx qy qz) =
  modeExt
    (negatedLeftCancellationScalar px qx)
    (negatedLeftCancellationScalar py qy)
    (negatedLeftCancellationScalar pz qz)

lowOutputDisplacementExact :
  (tau : Physical.PhysicalTriadIncidence) →
  Z3.addMode (Z3.negateMode (Physical.q tau)) (Physical.k tau)
  ≡ Physical.p tau
lowOutputDisplacementExact tau =
  trans
    (cong
      (Z3.addMode (Z3.negateMode (Physical.q tau)))
      (sym (Physical.resonance tau)))
    (negatedLeftModeCancellation (Physical.p tau) (Physical.q tau))

data LiteralTaylorEndpointGeometry
    (tau : Physical.PhysicalTriadIncidence) : Set where

  lowAdvectorEndpoints :
    Infinity.infinityNorm (Physical.p tau)
      ≤ Infinity.infinityNorm (Physical.q tau) →
    Infinity.infinityNorm (Physical.p tau)
      ≤ Infinity.infinityNorm (Physical.k tau) →
    Width.WithinOne
      (Shell.shellIndex (Physical.q tau))
      (Shell.shellIndex (Physical.k tau)) →
    Z3.addMode (Physical.q tau) (Physical.p tau) ≡ Physical.k tau →
    LiteralTaylorEndpointGeometry tau

  lowInputEndpoints :
    Infinity.infinityNorm (Physical.q tau)
      ≤ Infinity.infinityNorm (Physical.p tau) →
    Infinity.infinityNorm (Physical.q tau)
      ≤ Infinity.infinityNorm (Physical.k tau) →
    Width.WithinOne
      (Shell.shellIndex (Physical.p tau))
      (Shell.shellIndex (Physical.k tau)) →
    Z3.addMode (Physical.p tau) (Physical.q tau) ≡ Physical.k tau →
    LiteralTaylorEndpointGeometry tau

  lowOutputEndpoints :
    Infinity.infinityNorm (Physical.k tau)
      ≤ Infinity.infinityNorm (Physical.p tau) →
    Infinity.infinityNorm (Physical.k tau)
      ≤ Infinity.infinityNorm (Physical.q tau) →
    Width.WithinOne
      (Shell.shellIndex (Physical.p tau))
      (Shell.shellIndex (Physical.q tau)) →
    Z3.addMode (Z3.negateMode (Physical.q tau)) (Physical.k tau)
      ≡ Physical.p tau →
    LiteralTaylorEndpointGeometry tau

literalTaylorEndpointGeometry :
  (tau : Physical.PhysicalTriadIncidence) → LiteralTaylorEndpointGeometry tau
literalTaylorEndpointGeometry tau
  with Split.resonantDominantLowLegSplit tau
... | Split.lowP p≤q p≤k qkWithin =
      lowAdvectorEndpoints p≤q p≤k qkWithin
        (trans
          (modeAddCommutative (Physical.q tau) (Physical.p tau))
          (Physical.resonance tau))
... | Split.lowQ q≤p q≤k pkWithin =
      lowInputEndpoints q≤p q≤k pkWithin (Physical.resonance tau)
... | Split.lowK k≤p k≤q pqWithin =
      lowOutputEndpoints k≤p k≤q pqWithin
        (lowOutputDisplacementExact tau)

round68TaylorDisplacementIsLiteralLowLeg : Bool
round68TaylorDisplacementIsLiteralLowLeg = true

round68TaylorDisplacementIsLiteralLowLegIsTrue :
  round68TaylorDisplacementIsLiteralLowLeg ≡ true
round68TaylorDisplacementIsLiteralLowLegIsTrue = refl
