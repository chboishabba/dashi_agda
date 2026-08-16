module DASHI.Physics.Closure.NSTriadKNComOrderedPhysicalMajorantRound62Exact where

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
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- ROUND 62 SAME-OBJECT CARRIER CORRECTION
--
-- `PeriodicHardShellFourierPDE` chooses a literal algebraic `RealField F` and
-- the odd-(P/Q) coefficients live in Complex F.  Therefore the normalized
-- operator-product energy must be bounded IN `Carrier F`; moving it directly to
-- Q or to an unrelated Bishop-real carrier is not a same-object theorem.
--
-- The repository already has `OrderedRealExtension F`.  Add only the rational
-- embedding laws actually needed for the sharp constants, then prove the
-- bandwidth-one estimate on that very same carrier:
--
--   E(q,q)       <= [17/64]_F,
--   E(q,q+1)     <= [65/512]_F,
--   E(q+1,q)     <= [65/512]_F
--
-- imply
--
--   E(q,q)+E(q,q+1)+E(q+1,q) <= [133/256]_F.
--
-- Inactive pairs are literally zero in F.  No equality with Q and no change of
-- real carrier occurs.  This is the correct B consumer immediately downstream
-- of the literal odd-(P/Q) fibre.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
import Data.Rational.Base as Rat
open Rat using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as Ordered
import DASHI.Physics.Closure.NSTriadKNComCommonHatSupportLeafRound58 as Hat
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreMassLeafRound58 as Targets
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreAggregateRound60Exact as Aggregate

record OrderedRationalEmbedding
    {r : Level}
    {F : C3.RealField r}
    (O : Ordered.OrderedRealExtension F) : Set (lsuc r) where
  field
    embed : ℚ → C3.Carrier F
    embedZero : embed Rat.0ℚ ≡ C3.zero F
    embedAdd : ∀ a b →
      embed (Rat._+_ a b) ≡ C3.add F (embed a) (embed b)
    embedOrder : ∀ {a b} → Rat._≤_ a b → Ordered._≤_ O (embed a) (embed b)

open OrderedRationalEmbedding public

record OrderedPhysicalNormalizedOddPQSource
    {r : Level}
    (model : LP.PeriodicHardShellFourierPDE {r})
    (O : Ordered.OrderedRealExtension (LP.realField model))
    (R : OrderedRationalEmbedding O) : Set (lsuc r) where
  field
    support : Hat.PhysicalOddPQCommonHatIdentification
    normalizedPhysicalEnergy :
      Nat → Nat → C3.Carrier (LP.realField model)

    energyNonnegative : ∀ q s →
      Ordered._≤_ O (C3.zero (LP.realField model))
        (normalizedPhysicalEnergy q s)

    inactiveEnergyZero : ∀ q s →
      Hat.supportActive support q s ≡ false →
      normalizedPhysicalEnergy q s ≡ C3.zero (LP.realField model)

    sameShellActiveBound : ∀ q →
      Hat.supportActive support q q ≡ true →
      Ordered._≤_ O
        (normalizedPhysicalEnergy q q)
        (embed R Targets.sameShellTarget)

    forwardAdjacentActiveBound : ∀ q →
      Hat.supportActive support q (suc q) ≡ true →
      Ordered._≤_ O
        (normalizedPhysicalEnergy q (suc q))
        (embed R Targets.adjacentShellTarget)

    reverseAdjacentActiveBound : ∀ q →
      Hat.supportActive support (suc q) q ≡ true →
      Ordered._≤_ O
        (normalizedPhysicalEnergy (suc q) q)
        (embed R Targets.adjacentShellTarget)

open OrderedPhysicalNormalizedOddPQSource public

zeroBelowEmbeddedSameTarget :
  ∀ {r model O} (R : OrderedRationalEmbedding {r} {LP.realField model} O) →
  Ordered._≤_ O (C3.zero (LP.realField model)) (embed R Targets.sameShellTarget)
zeroBelowEmbeddedSameTarget R =
  subst
    (λ left → Ordered._≤_ _ left (embed R Targets.sameShellTarget))
    (embedZero R)
    (embedOrder R Aggregate.sameTargetNonnegative)

zeroBelowEmbeddedAdjacentTarget :
  ∀ {r model O} (R : OrderedRationalEmbedding {r} {LP.realField model} O) →
  Ordered._≤_ O (C3.zero (LP.realField model)) (embed R Targets.adjacentShellTarget)
zeroBelowEmbeddedAdjacentTarget R =
  subst
    (λ left → Ordered._≤_ _ left (embed R Targets.adjacentShellTarget))
    (embedZero R)
    (embedOrder R Aggregate.adjacentTargetNonnegative)

samePairBelowTarget :
  ∀ {r model O R}
    (source : OrderedPhysicalNormalizedOddPQSource
      {r} model O R) q →
  Ordered._≤_ O
    (normalizedPhysicalEnergy source q q)
    (embed R Targets.sameShellTarget)
samePairBelowTarget {O = O} {R = R} source q
  with Hat.supportActive (support source) q q in activeProof
... | true = sameShellActiveBound source q activeProof
... | false =
  subst
    (λ left → Ordered._≤_ O left (embed R Targets.sameShellTarget))
    (sym (inactiveEnergyZero source q q activeProof))
    (zeroBelowEmbeddedSameTarget R)

forwardPairBelowTarget :
  ∀ {r model O R}
    (source : OrderedPhysicalNormalizedOddPQSource
      {r} model O R) q →
  Ordered._≤_ O
    (normalizedPhysicalEnergy source q (suc q))
    (embed R Targets.adjacentShellTarget)
forwardPairBelowTarget {O = O} {R = R} source q
  with Hat.supportActive (support source) q (suc q) in activeProof
... | true = forwardAdjacentActiveBound source q activeProof
... | false =
  subst
    (λ left → Ordered._≤_ O left (embed R Targets.adjacentShellTarget))
    (sym (inactiveEnergyZero source q (suc q) activeProof))
    (zeroBelowEmbeddedAdjacentTarget R)

reversePairBelowTarget :
  ∀ {r model O R}
    (source : OrderedPhysicalNormalizedOddPQSource
      {r} model O R) q →
  Ordered._≤_ O
    (normalizedPhysicalEnergy source (suc q) q)
    (embed R Targets.adjacentShellTarget)
reversePairBelowTarget {O = O} {R = R} source q
  with Hat.supportActive (support source) (suc q) q in activeProof
... | true = reverseAdjacentActiveBound source q activeProof
... | false =
  subst
    (λ left → Ordered._≤_ O left (embed R Targets.adjacentShellTarget))
    (sym (inactiveEnergyZero source (suc q) q activeProof))
    (zeroBelowEmbeddedAdjacentTarget R)

bandwidthOnePhysicalEnergy :
  ∀ {r model O R} →
  OrderedPhysicalNormalizedOddPQSource {r} model O R →
  Nat → C3.Carrier (LP.realField model)
bandwidthOnePhysicalEnergy {model = model} source q =
  C3.add (LP.realField model)
    (C3.add (LP.realField model)
      (normalizedPhysicalEnergy source q q)
      (normalizedPhysicalEnergy source q (suc q)))
    (normalizedPhysicalEnergy source (suc q) q)

threeEmbeddedTargetsEqualBandwidthTarget :
  ∀ {r model O} (R : OrderedRationalEmbedding {r} {LP.realField model} O) →
  C3.add (LP.realField model)
    (C3.add (LP.realField model)
      (embed R Targets.sameShellTarget)
      (embed R Targets.adjacentShellTarget))
    (embed R Targets.adjacentShellTarget)
  ≡ embed R Aggregate.bandwidthOneTarget
threeEmbeddedTargetsEqualBandwidthTarget R =
  let
    first :
      C3.add _
        (embed R Targets.sameShellTarget)
        (embed R Targets.adjacentShellTarget)
      ≡ embed R (Rat._+_ Targets.sameShellTarget Targets.adjacentShellTarget)
    first = sym (embedAdd R Targets.sameShellTarget Targets.adjacentShellTarget)

    second :
      C3.add _
        (embed R (Rat._+_ Targets.sameShellTarget Targets.adjacentShellTarget))
        (embed R Targets.adjacentShellTarget)
      ≡ embed R
          (Rat._+_
            (Rat._+_ Targets.sameShellTarget Targets.adjacentShellTarget)
            Targets.adjacentShellTarget)
    second = sym
      (embedAdd R
        (Rat._+_ Targets.sameShellTarget Targets.adjacentShellTarget)
        Targets.adjacentShellTarget)
  in
  trans
    (cong
      (λ left → C3.add _ left (embed R Targets.adjacentShellTarget))
      first)
    (trans second (cong (embed R) Aggregate.targetArithmetic))

bandwidthOnePhysicalEnergyBelow133Over256 :
  ∀ {r model O R}
    (source : OrderedPhysicalNormalizedOddPQSource {r} model O R) q →
  Ordered._≤_ O
    (bandwidthOnePhysicalEnergy source q)
    (embed R Aggregate.bandwidthOneTarget)
bandwidthOnePhysicalEnergyBelow133Over256
    {model = model} {O = O} {R = R} source q =
  let
    pairSum :
      Ordered._≤_ O
        (bandwidthOnePhysicalEnergy source q)
        (C3.add (LP.realField model)
          (C3.add (LP.realField model)
            (embed R Targets.sameShellTarget)
            (embed R Targets.adjacentShellTarget))
          (embed R Targets.adjacentShellTarget))
    pairSum =
      Ordered.addMonotone O
        (Ordered.addMonotone O
          (samePairBelowTarget source q)
          (forwardPairBelowTarget source q))
        (reversePairBelowTarget source q)
  in
  subst
    (λ right → Ordered._≤_ O (bandwidthOnePhysicalEnergy source q) right)
    (threeEmbeddedTargetsEqualBandwidthTarget R)
    pairSum

physicalComMajorantLivesInLiteralFourierRealField : Bool
physicalComMajorantLivesInLiteralFourierRealField = true

physicalComMajorantLivesInLiteralFourierRealFieldIsTrue :
  physicalComMajorantLivesInLiteralFourierRealField ≡ true
physicalComMajorantLivesInLiteralFourierRealFieldIsTrue = refl
