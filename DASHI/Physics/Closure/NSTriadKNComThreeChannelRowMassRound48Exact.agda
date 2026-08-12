module DASHI.Physics.Closure.NSTriadKNComThreeChannelRowMassRound48Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- DASHI CONTRIBUTION
--
-- Round 47 reduced the physical Com support to the three possible channels
-- seen from one shell q:
--
--   (q,q), (q,q+1), (q+1,q).
--
-- The exact six-three targets are 17/64 for the same-shell channel and 65/512
-- for each adjacent channel.  Combining the active bound with exact
-- off-support annihilation makes each bound unconditional.  Hence the whole
-- three-channel row has mass at most
--
--   17/64 + 2(65/512) = 133/256 < 1.
--
-- This is an operator-support arithmetic fact only.  It is NOT relabelled as
-- the final Com viscosity tax; a physical pre-absorption theorem must still
-- show how this row mass enters the actual owner production estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _/_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_; _<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNComSameAdjacentActiveRound47Exact as Active

threeChannelTarget : ℚ
threeChannelTarget = Int.+ 133 / 256

sameShellTargetNonnegative : 0ℚ ≤ Active.sameShellTarget
sameShellTargetNonnegative =
  toWitness {a? = 0ℚ ≤? Active.sameShellTarget} _

adjacentShellTargetNonnegative : 0ℚ ≤ Active.adjacentShellTarget
adjacentShellTargetNonnegative =
  toWitness {a? = 0ℚ ≤? Active.adjacentShellTarget} _

threeChannelTargetExact :
  Active.sameShellTarget
    + Active.adjacentShellTarget
    + Active.adjacentShellTarget
  ≡ threeChannelTarget
threeChannelTargetExact = solve []

threeChannelTargetStrictlyBelowOne : threeChannelTarget < 1ℚ
threeChannelTargetStrictlyBelowOne =
  toWitness {a? = threeChannelTarget <? 1ℚ} _

sameShellBoundUnconditional :
  ∀ {skeleton identification}
    (bounds : Active.SameAdjacentPhysicalComBounds skeleton identification) q →
  Active.physicalPairProduct skeleton q q ≤ Active.sameShellTarget
sameShellBoundUnconditional {skeleton} bounds q
  with Active.supportActive skeleton q q
... | true = Active.physicalComSameShellActiveBound bounds q refl
... | false =
  subst
    (λ product → product ≤ Active.sameShellTarget)
    (sym (Active.inactiveSupportAnnihilatesPairProduct skeleton q q refl))
    sameShellTargetNonnegative

forwardAdjacentBoundUnconditional :
  ∀ {skeleton identification}
    (bounds : Active.SameAdjacentPhysicalComBounds skeleton identification) q →
  Active.physicalPairProduct skeleton q (suc q)
  ≤ Active.adjacentShellTarget
forwardAdjacentBoundUnconditional {skeleton} bounds q
  with Active.supportActive skeleton q (suc q)
... | true = Active.physicalComAdjacentShellActiveBound bounds q refl
... | false =
  subst
    (λ product → product ≤ Active.adjacentShellTarget)
    (sym (Active.inactiveSupportAnnihilatesPairProduct skeleton q (suc q) refl))
    adjacentShellTargetNonnegative

backwardAdjacentBoundUnconditional :
  ∀ {skeleton identification}
    (bounds : Active.SameAdjacentPhysicalComBounds skeleton identification) q →
  Active.physicalPairProduct skeleton (suc q) q
  ≤ Active.adjacentShellTarget
backwardAdjacentBoundUnconditional {skeleton} bounds q
  with Active.supportActive skeleton (suc q) q
... | true = Active.physicalComReverseAdjacentShellActiveBound bounds q refl
... | false =
  subst
    (λ product → product ≤ Active.adjacentShellTarget)
    (sym (Active.inactiveSupportAnnihilatesPairProduct skeleton (suc q) q refl))
    adjacentShellTargetNonnegative

physicalThreeChannelRowMass :
  Active.PhysicalOddPQSupportSkeleton → Nat → ℚ
physicalThreeChannelRowMass skeleton q =
  Active.physicalPairProduct skeleton q q
  + Active.physicalPairProduct skeleton q (suc q)
  + Active.physicalPairProduct skeleton (suc q) q

physicalThreeChannelRowMassBelowTarget :
  ∀ {skeleton identification}
    (bounds : Active.SameAdjacentPhysicalComBounds skeleton identification) q →
  physicalThreeChannelRowMass skeleton q ≤ threeChannelTarget
physicalThreeChannelRowMassBelowTarget {skeleton} bounds q =
  let
    summed :
      physicalThreeChannelRowMass skeleton q
      ≤ Active.sameShellTarget
        + Active.adjacentShellTarget
        + Active.adjacentShellTarget
    summed =
      ℚP.+-mono-≤
        (ℚP.+-mono-≤
          (sameShellBoundUnconditional bounds q)
          (forwardAdjacentBoundUnconditional bounds q))
        (backwardAdjacentBoundUnconditional bounds q)
  in
  subst
    (λ upper → physicalThreeChannelRowMass skeleton q ≤ upper)
    threeChannelTargetExact
    summed

physicalThreeChannelRowMassStrictlyBelowOne :
  ∀ {skeleton identification}
    (bounds : Active.SameAdjacentPhysicalComBounds skeleton identification) q →
  physicalThreeChannelRowMass skeleton q < 1ℚ
physicalThreeChannelRowMassStrictlyBelowOne bounds q =
  ℚP.≤-<-trans
    (physicalThreeChannelRowMassBelowTarget bounds q)
    threeChannelTargetStrictlyBelowOne

comThreeChannelRowMassExact : Bool
comThreeChannelRowMassExact = true

comThreeChannelRowMassExactIsTrue :
  comThreeChannelRowMassExact ≡ true
comThreeChannelRowMassExactIsTrue = refl
