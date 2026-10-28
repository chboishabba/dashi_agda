module DASHI.Foundations.QuinticOverlappingThreeCyclesExact where

------------------------------------------------------------------------
-- QUINTIC COMMUTATOR WITNESS, NOT YET THE GLOBAL A5 PERFECTNESS THEOREM.
-- Classical group theory provenance: Galois (1830--1832), Jordan (1870),
-- modern Dixon--Mortimer (1996), Serre (1977).
--
-- Let A=(0 1 2), B=(2 3 4) in S5, sharing precisely index 2.
-- Define C=[A,B], D=[A^-1,B^-1].
-- Then [C,D]=A pointwise; swapping A and B yields B analogously.
-- This is an explicit DOUBLE COMMUTATOR witness with no postulates.
-- It matches the video's central five-root demonstration.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

data Point5 : Set where
  p0 p1 p2 p3 p4 : Point5

Map5 : Set
Map5 = Point5 → Point5

identity5 : Map5
identity5 x = x

compose5 : Map5 → Map5 → Map5
compose5 f g x = f (g x)

cycleA cycleAInverse cycleB cycleBInverse : Map5
  cycleA p0 = p1
cycleA p1 = p2
cycleA p2 = p0
cycleA p3 = p3
cycleA p4 = p4
  cycleAInverse p0 = p2
cycleAInverse p1 = p0
cycleAInverse p2 = p1
cycleAInverse p3 = p3
cycleAInverse p4 = p4
  cycleB p0 = p0
cycleB p1 = p1
cycleB p2 = p3
cycleB p3 = p4
cycleB p4 = p2
  cycleBInverse p0 = p0
cycleBInverse p1 = p1
cycleBInverse p2 = p4
cycleBInverse p3 = p2
cycleBInverse p4 = p3

-- Inverses are proved on every point; functions stay extensional.
cycleAInverseLaw :
  (x : Point5) → compose5 cycleA cycleAInverse x ≡ x
cycleAInverseLaw p0 = refl
cycleAInverseLaw p1 = refl
cycleAInverseLaw p2 = refl
cycleAInverseLaw p3 = refl
cycleAInverseLaw p4 = refl

cycleBInverseLaw :
  (x : Point5) → compose5 cycleB cycleBInverse x ≡ x
cycleBInverseLaw p0 = refl
cycleBInverseLaw p1 = refl
cycleBInverseLaw p2 = refl
cycleBInverseLaw p3 = refl
cycleBInverseLaw p4 = refl

commutatorWithInverses :
  Map5 → Map5 → Map5 → Map5 → Map5
commutatorWithInverses f g inverseF inverseG =
  compose5 (compose5 (compose5 f g) inverseF) inverseG

firstCommutator : Map5
firstCommutator =
  commutatorWithInverses cycleA cycleB cycleAInverse cycleBInverse

inverseFirstCommutator : Map5
inverseFirstCommutator =
  compose5
    (compose5 (compose5 cycleB cycleA) cycleBInverse)
    cycleAInverse

secondCommutator : Map5
secondCommutator =
  commutatorWithInverses cycleAInverse cycleBInverse cycleA cycleB

inverseSecondCommutator : Map5
inverseSecondCommutator =
  compose5
    (compose5 (compose5 cycleBInverse cycleAInverse) cycleB)
    cycleA

firstCommutatorInverseLaw :
  (x : Point5) →
  compose5 firstCommutator inverseFirstCommutator x ≡ x
firstCommutatorInverseLaw p0 = refl
firstCommutatorInverseLaw p1 = refl
firstCommutatorInverseLaw p2 = refl
firstCommutatorInverseLaw p3 = refl
firstCommutatorInverseLaw p4 = refl

secondCommutatorInverseLaw :
  (x : Point5) →
  compose5 secondCommutator inverseSecondCommutator x ≡ x
secondCommutatorInverseLaw p0 = refl
secondCommutatorInverseLaw p1 = refl
secondCommutatorInverseLaw p2 = refl
secondCommutatorInverseLaw p3 = refl
secondCommutatorInverseLaw p4 = refl

doubleCommutatorRecoversA : (x : Point5) →
  commutatorWithInverses
    firstCommutator secondCommutator
    inverseFirstCommutator inverseSecondCommutator
    x
  ≡ cycleA x
doubleCommutatorRecoversA p0 = refl
doubleCommutatorRecoversA p1 = refl
doubleCommutatorRecoversA p2 = refl
doubleCommutatorRecoversA p3 = refl
doubleCommutatorRecoversA p4 = refl

-- Reverse roles to recover the OTHER three-cycle rather than only A^-1.
firstCommutatorB : Map5
firstCommutatorB =
  commutatorWithInverses cycleB cycleA cycleBInverse cycleAInverse

inverseFirstCommutatorB : Map5
inverseFirstCommutatorB =
  compose5
    (compose5 (compose5 cycleA cycleB) cycleAInverse)
    cycleBInverse

secondCommutatorB : Map5
secondCommutatorB =
  commutatorWithInverses cycleBInverse cycleAInverse cycleB cycleA

inverseSecondCommutatorB : Map5
inverseSecondCommutatorB =
  compose5
    (compose5 (compose5 cycleAInverse cycleBInverse) cycleA)
    cycleB

doubleCommutatorRecoversB : (x : Point5) →
  commutatorWithInverses
    firstCommutatorB secondCommutatorB
    inverseFirstCommutatorB inverseSecondCommutatorB
    x
  ≡ cycleB x
doubleCommutatorRecoversB p0 = refl
doubleCommutatorRecoversB p1 = refl
doubleCommutatorRecoversB p2 = refl
doubleCommutatorRecoversB p3 = refl
doubleCommutatorRecoversB p4 = refl

-- Exact negative gates: even this closed two-generator computation alone
-- does not establish the whole A5 is simple/perfect, all S5 conjugacy
-- classes, a polynomial Galois group, or a quintic impossibility theorem.
data TwoCyclesAloneProveGenericQuinticInsolubility : Set where

noQuinticTheoremFromTwoCycleWitnessAlone :
  TwoCyclesAloneProveGenericQuinticInsolubility → ⊥
noQuinticTheoremFromTwoCycleWitnessAlone ()
