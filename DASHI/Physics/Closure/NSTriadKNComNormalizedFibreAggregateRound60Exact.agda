module DASHI.Physics.Closure.NSTriadKNComNormalizedFibreAggregateRound60Exact where

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
-- ROUND 60 CONTRIBUTION
--
-- Keep the complete B falsifier on the lightweight physical source graph.
-- Active same/adjacent estimates extend to all three bandwidth-one pairs by
-- exact off-support annihilation, and exact rational arithmetic gives
--
--   17/64 + 65/512 + 65/512 = 133/256.
--
-- This file intentionally does NOT import the older Cotlar/Schur envelope
-- graph.  It can therefore be checked independently when the legacy graph is
-- too expensive to elaborate.  No physical estimate is manufactured: the
-- three active inequalities remain precisely the fields of source.bounds.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_; _/_)
import Data.Integer.Base as Int
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNComCommonHatSupportLeafRound58 as Hat
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreMassLeafRound58 as Gram
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreSourceRound60Exact as Source

bandwidthOneTarget : ℚ
bandwidthOneTarget = Int.+ 133 / 256

targetArithmetic :
  Gram.sameShellTarget
    + Gram.adjacentShellTarget
    + Gram.adjacentShellTarget
  ≡ bandwidthOneTarget
targetArithmetic = solve []

sameTargetNonnegative : 0ℚ ≤ Gram.sameShellTarget
sameTargetNonnegative = toWitness {a? = 0ℚ ≤? Gram.sameShellTarget} _

adjacentTargetNonnegative : 0ℚ ≤ Gram.adjacentShellTarget
adjacentTargetNonnegative =
  toWitness {a? = 0ℚ ≤? Gram.adjacentShellTarget} _

samePairBelow :
  (source : Source.PhysicalNormalizedOddPQSource) →
  (q : Nat) →
  Gram.pairProduct (Source.realization source) q q ≤ Gram.sameShellTarget
samePairBelow source q
  with Hat.supportActive (Source.support source) q q
... | true = Gram.sameShellBound (Source.bounds source) q refl
... | false =
  subst
    (λ left → left ≤ Gram.sameShellTarget)
    (sym (Source.inactiveSupportAnnihilatesPairProduct source q q refl))
    sameTargetNonnegative

forwardAdjacentPairBelow :
  (source : Source.PhysicalNormalizedOddPQSource) →
  (q : Nat) →
  Gram.pairProduct (Source.realization source) q (suc q)
  ≤ Gram.adjacentShellTarget
forwardAdjacentPairBelow source q
  with Hat.supportActive (Source.support source) q (suc q)
... | true = Gram.forwardAdjacentBound (Source.bounds source) q refl
... | false =
  subst
    (λ left → left ≤ Gram.adjacentShellTarget)
    (sym
      (Source.inactiveSupportAnnihilatesPairProduct
        source q (suc q) refl))
    adjacentTargetNonnegative

reverseAdjacentPairBelow :
  (source : Source.PhysicalNormalizedOddPQSource) →
  (q : Nat) →
  Gram.pairProduct (Source.realization source) (suc q) q
  ≤ Gram.adjacentShellTarget
reverseAdjacentPairBelow source q
  with Hat.supportActive (Source.support source) (suc q) q
... | true = Gram.reverseAdjacentBound (Source.bounds source) q refl
... | false =
  subst
    (λ left → left ≤ Gram.adjacentShellTarget)
    (sym
      (Source.inactiveSupportAnnihilatesPairProduct
        source (suc q) q refl))
    adjacentTargetNonnegative

normalizedOddPQBandwidthOneMass :
  Source.PhysicalNormalizedOddPQSource → Nat → ℚ
normalizedOddPQBandwidthOneMass source q =
  Gram.pairProduct (Source.realization source) q q
    + Gram.pairProduct (Source.realization source) q (suc q)
    + Gram.pairProduct (Source.realization source) (suc q) q

normalizedOddPQBandwidthOneMassBelow133Over256 :
  (source : Source.PhysicalNormalizedOddPQSource) →
  ∀ q →
  normalizedOddPQBandwidthOneMass source q ≤ bandwidthOneTarget
normalizedOddPQBandwidthOneMassBelow133Over256 source q =
  let
    summed :
      normalizedOddPQBandwidthOneMass source q
      ≤ Gram.sameShellTarget
        + Gram.adjacentShellTarget
        + Gram.adjacentShellTarget
    summed =
      ℚP.+-mono-≤
        (ℚP.+-mono-≤
          (samePairBelow source q)
          (forwardAdjacentPairBelow source q))
        (reverseAdjacentPairBelow source q)
  in
  subst
    (λ upper → normalizedOddPQBandwidthOneMass source q ≤ upper)
    targetArithmetic
    summed
