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
-- Route the canonical normalized odd-(P/Q) source all the way through the
-- mature squared whole-fibre endpoint.  The source stores the literal active
-- support and proves off-support annihilation.  Therefore the same/adjacent
-- inequalities extend from ACTIVE pairs to every shell pair by a Boolean case
-- split: inactive pairs have exactly zero normalized Gram energy.
--
-- This closes the B transport gap:
--
--   same <= 17/64,
--   forward adjacent <= 65/512,
--   reverse adjacent <= 65/512
--
-- imply, on the same canonical source,
--
--   same + forward + reverse <= 133/256.
--
-- No physical estimate is manufactured here: the three active inequalities
-- remain precisely the fields of PhysicalNormalizedOddPQSource.bounds.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNComCommonHatSupportLeafRound58 as Hat
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreMassLeafRound58 as Gram
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreSourceRound60Exact as Source
import DASHI.Physics.Closure.NSTriadKNComLiteralSameAdjacentFibreRound55Exact as Whole

sameTargetAgreement : Gram.sameShellTarget ≡ Whole.same
sameTargetAgreement = solve []

adjacentTargetAgreement : Gram.adjacentShellTarget ≡ Whole.adjacent
adjacentTargetAgreement = solve []

sameTargetNonnegative : 0ℚ ≤ Whole.same
sameTargetNonnegative = toWitness {a? = 0ℚ ≤? Whole.same} _

adjacentTargetNonnegative : 0ℚ ≤ Whole.adjacent
adjacentTargetNonnegative = toWitness {a? = 0ℚ ≤? Whole.adjacent} _

samePairBelow :
  (source : Source.PhysicalNormalizedOddPQSource) →
  (q : Nat) →
  Gram.pairProduct (Source.realization source) q q ≤ Whole.same
samePairBelow source q
  with Hat.supportActive (Source.support source) q q
... | true =
  subst
    (λ target → Gram.pairProduct (Source.realization source) q q ≤ target)
    sameTargetAgreement
    (Gram.sameShellBound (Source.bounds source) q refl)
... | false =
  subst
    (λ left → left ≤ Whole.same)
    (sym (Source.inactiveSupportAnnihilatesPairProduct source q q refl))
    sameTargetNonnegative

forwardAdjacentPairBelow :
  (source : Source.PhysicalNormalizedOddPQSource) →
  (q : Nat) →
  Gram.pairProduct (Source.realization source) q (suc q) ≤ Whole.adjacent
forwardAdjacentPairBelow source q
  with Hat.supportActive (Source.support source) q (suc q)
... | true =
  subst
    (λ target →
      Gram.pairProduct (Source.realization source) q (suc q) ≤ target)
    adjacentTargetAgreement
    (Gram.forwardAdjacentBound (Source.bounds source) q refl)
... | false =
  subst
    (λ left → left ≤ Whole.adjacent)
    (sym
      (Source.inactiveSupportAnnihilatesPairProduct
        source q (suc q) refl))
    adjacentTargetNonnegative

reverseAdjacentPairBelow :
  (source : Source.PhysicalNormalizedOddPQSource) →
  (q : Nat) →
  Gram.pairProduct (Source.realization source) (suc q) q ≤ Whole.adjacent
reverseAdjacentPairBelow source q
  with Hat.supportActive (Source.support source) (suc q) q
... | true =
  subst
    (λ target →
      Gram.pairProduct (Source.realization source) (suc q) q ≤ target)
    adjacentTargetAgreement
    (Gram.reverseAdjacentBound (Source.bounds source) q refl)
... | false =
  subst
    (λ left → left ≤ Whole.adjacent)
    (sym
      (Source.inactiveSupportAnnihilatesPairProduct
        source (suc q) q refl))
    adjacentTargetNonnegative

literalWholeFibreMassesAt :
  Source.PhysicalNormalizedOddPQSource → Nat → Whole.LiteralWholeFibreMasses
literalWholeFibreMassesAt source q = record
  { sameMass = Gram.pairProduct (Source.realization source) q q
  ; forwardAdjacentMass =
      Gram.pairProduct (Source.realization source) q (suc q)
  ; reverseAdjacentMass =
      Gram.pairProduct (Source.realization source) (suc q) q
  ; sameMassBelow = samePairBelow source q
  ; forwardAdjacentMassBelow = forwardAdjacentPairBelow source q
  ; reverseAdjacentMassBelow = reverseAdjacentPairBelow source q
  }

normalizedOddPQBandwidthOneMass :
  Source.PhysicalNormalizedOddPQSource → Nat → ℚ
normalizedOddPQBandwidthOneMass source q =
  Whole.wholeBandwidthOneMass (literalWholeFibreMassesAt source q)

normalizedOddPQBandwidthOneMassBelow133Over256 :
  (source : Source.PhysicalNormalizedOddPQSource) →
  ∀ q →
  normalizedOddPQBandwidthOneMass source q ≤ Whole.target
normalizedOddPQBandwidthOneMassBelow133Over256 source q =
  Whole.wholeBandwidthOneMassBelow133Over256
    (literalWholeFibreMassesAt source q)
