module DASHI.Analysis.CollatzSyracuseConstructiveSurvivorExtractionExact where

------------------------------------------------------------------------
-- CONSTRUCTIVE SURVIVOR EXTRACTION
--
-- The inverse-limit obstruction isolates a genuine constructive asymmetry:
--
--   no coherent all-horizon survivor
--
-- gives only a double-negated finite descent witness in constructive logic.
-- It does not, by itself, choose the finite descent horizon.
--
-- This owner separates two routes cleanly:
--
--   1. FINITE BARRIER: if one explicit finite horizon cannot survive at every
--      time 0..h, decidability of literal Nat comparison searches that finite
--      horizon and returns an actual strict-descent witness constructively;
--
--   2. UNBOUNDED NEGATION: absence of an all-horizon survivor gives
--      double-negated strict descent.  A separately supplied Nat-search Markov
--      principle converts that double negation into the witness.  The repo does
--      not silently own that principle.
--
-- The finite-barrier route is proved equivalent to the existing literal
-- strict-descent producer.  It is therefore an extraction normal form, not a
-- weaker substitute for the remaining Collatz-strength mathematics.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (_<_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)
import Data.Nat.Properties as NatP

import DASHI.Foundations.StratifiedResolutionTowerExact as Tower
import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.Analysis.CollatzSyracuseUniversalStoppingCompilerExact as Stop
import DASHI.Analysis.CollatzSyracuseResidualInverseLimitObstructionExact as Inverse

------------------------------------------------------------------------
-- Literal one-horizon descent predicate and its exact decision procedure.
------------------------------------------------------------------------

DescentAt : Syracuse.PositiveNat → Nat → Set
DescentAt x m =
  Syracuse.toNat (Syracuse.syracuseIterate m x)
  < Syracuse.toNat x

decDescentAt :
  (x : Syracuse.PositiveNat) →
  (m : Nat) →
  Dec (DescentAt x m)
decDescentAt x m =
  NatP._<?_
    (Syracuse.toNat (Syracuse.syracuseIterate m x))
    (Syracuse.toNat x)

------------------------------------------------------------------------
-- A recursive finite prefix search surface.
--
-- `DescentBy x h` means that one of the literal horizons 0..h descends.
-- `SurvivesThrough x h` means that none of those same literal horizons does.
-- They share the SAME Syracuse orbit and start x; this is not a parity-word
-- proxy or finite residue surrogate.
------------------------------------------------------------------------

data DescentBy (x : Syracuse.PositiveNat) : Nat → Set where
  descentAtZero :
    DescentAt x zero →
    DescentBy x zero

  descentEarlier :
    {h : Nat} →
    DescentBy x h →
    DescentBy x (suc h)

  descentAtLast :
    {h : Nat} →
    DescentAt x (suc h) →
    DescentBy x (suc h)

SurvivesThrough : Syracuse.PositiveNat → Nat → Set
SurvivesThrough x zero =
  ¬ DescentAt x zero
SurvivesThrough x (suc h) =
  SurvivesThrough x h ×
  (¬ DescentAt x (suc h))

decDescentBy :
  (x : Syracuse.PositiveNat) →
  (h : Nat) →
  Dec (DescentBy x h)
decDescentBy x zero with decDescentAt x zero
... | yes descent = yes (descentAtZero descent)
... | no noDescent =
  no (λ { (descentAtZero descent) → noDescent descent })
decDescentBy x (suc h) with decDescentBy x h | decDescentAt x (suc h)
... | yes earlier | yes current = yes (descentEarlier earlier)
... | yes earlier | no noCurrent = yes (descentEarlier earlier)
... | no noEarlier | yes current = yes (descentAtLast current)
... | no noEarlier | no noCurrent =
  no
    (λ
      { (descentEarlier earlier) → noEarlier earlier
      ; (descentAtLast current) → noCurrent current
      })

survivesThroughIfNoDescentBy :
  (x : Syracuse.PositiveNat) →
  (h : Nat) →
  ¬ DescentBy x h →
  SurvivesThrough x h
survivesThroughIfNoDescentBy x zero noDescentBy =
  λ descent → noDescentBy (descentAtZero descent)
survivesThroughIfNoDescentBy x (suc h) noDescentBy =
  survivesThroughIfNoDescentBy
    x
    h
    (λ earlier → noDescentBy (descentEarlier earlier))
  ,
  (λ current → noDescentBy (descentAtLast current))

descentByToStrictDescent :
  {x : Syracuse.PositiveNat} {h : Nat} →
  DescentBy x h →
  Stop.StrictDescentWithin x
descentByToStrictDescent (descentAtZero descent) =
  zero , descent
descentByToStrictDescent (descentEarlier earlier) =
  descentByToStrictDescent earlier
descentByToStrictDescent (descentAtLast {h = h} descent) =
  suc h , descent

------------------------------------------------------------------------
-- FINITE BARRIER ROUTE: fully constructive.
------------------------------------------------------------------------

finiteBarrierExtractsDescent :
  (x : Syracuse.PositiveNat) →
  (h : Nat) →
  ¬ SurvivesThrough x h →
  Stop.StrictDescentWithin x
finiteBarrierExtractsDescent x h barrier with decDescentBy x h
... | yes witness = descentByToStrictDescent witness
... | no noWitness =
  ⊥-elim
    (barrier (survivesThroughIfNoDescentBy x h noWitness))

record FiniteSurvivorBarrierSource : Set₁ where
  field
    barrierHorizon :
      (x : Syracuse.PositiveNat) →
      1 < Syracuse.toNat x →
      Nat

    blocksCompleteSurvival :
      (x : Syracuse.PositiveNat) →
      (nontrivial : 1 < Syracuse.toNat x) →
      ¬ SurvivesThrough x (barrierHorizon x nontrivial)

open FiniteSurvivorBarrierSource public

finiteBarrierToLiteralStrictDescentSource :
  FiniteSurvivorBarrierSource →
  Stop.LiteralStrictDescentSource
finiteBarrierToLiteralStrictDescentSource source = record
  { descend = λ x nontrivial →
      finiteBarrierExtractsDescent
        x
        (barrierHorizon source x nontrivial)
        (blocksCompleteSurvival source x nontrivial)
  }

finiteBarrierToUniversalStopping :
  FiniteSurvivorBarrierSource →
  (x : Syracuse.PositiveNat) →
  Stop.ReachesOne x
finiteBarrierToUniversalStopping source =
  Stop.universalStoppingFromStrictDescent
    (finiteBarrierToLiteralStrictDescentSource source)

------------------------------------------------------------------------
-- Reverse compiler: a literal strict-descent witness itself supplies a finite
-- barrier at its witnessed horizon.  Thus the finite-barrier normal form does
-- not weaken the theorem-strength terminal obligation.
------------------------------------------------------------------------

descentAtBlocksSurvival :
  {x : Syracuse.PositiveNat} →
  (m : Nat) →
  DescentAt x m →
  ¬ SurvivesThrough x m
descentAtBlocksSurvival zero descent survival =
  survival descent
descentAtBlocksSurvival (suc m) descent survival =
  proj₂ survival descent

literalStrictDescentToFiniteBarrierSource :
  Stop.LiteralStrictDescentSource →
  FiniteSurvivorBarrierSource
literalStrictDescentToFiniteBarrierSource source = record
  { barrierHorizon = λ x nontrivial →
      proj₁ (Stop.descend source x nontrivial)
  ; blocksCompleteSurvival = λ x nontrivial →
      let witness = Stop.descend source x nontrivial
      in descentAtBlocksSurvival
           (proj₁ witness)
           (proj₂ witness)
  }

record FiniteBarrierStrictDescentEquivalence : Set₁ where
  constructor finiteBarrierStrictDescentEquivalence
  field
    barrierToDescent :
      FiniteSurvivorBarrierSource →
      Stop.LiteralStrictDescentSource

    descentToBarrier :
      Stop.LiteralStrictDescentSource →
      FiniteSurvivorBarrierSource

open FiniteBarrierStrictDescentEquivalence public

canonicalFiniteBarrierStrictDescentEquivalence :
  FiniteBarrierStrictDescentEquivalence
canonicalFiniteBarrierStrictDescentEquivalence =
  finiteBarrierStrictDescentEquivalence
    finiteBarrierToLiteralStrictDescentSource
    literalStrictDescentToFiniteBarrierSource

------------------------------------------------------------------------
-- UNBOUNDED NEGATION ROUTE: constructive result stops at double negation.
------------------------------------------------------------------------

NoInfiniteSurvivor : Syracuse.PositiveNat → Set
NoInfiniteSurvivor x =
  ¬ Inverse.AllHorizonSurvivor x

NoInverseSurvivorPoint : Syracuse.PositiveNat → Set₁
NoInverseSurvivorPoint x =
  ¬ Tower.InverseLimitPoint (Inverse.survivorTower x)

noInversePointToNoInfiniteSurvivor :
  {x : Syracuse.PositiveNat} →
  NoInverseSurvivorPoint x →
  NoInfiniteSurvivor x
noInversePointToNoInfiniteSurvivor noPoint allHorizon =
  noPoint (Inverse.inversePointFromAllHorizon allHorizon)

noInfiniteSurvivorGivesDoubleNegatedDescent :
  {x : Syracuse.PositiveNat} →
  NoInfiniteSurvivor x →
  ¬ (¬ Stop.StrictDescentWithin x)
noInfiniteSurvivorGivesDoubleNegatedDescent noInfinite noDescent =
  noInfinite
    (λ m descent →
      noDescent (m , descent))

noInversePointGivesDoubleNegatedDescent :
  {x : Syracuse.PositiveNat} →
  NoInverseSurvivorPoint x →
  ¬ (¬ Stop.StrictDescentWithin x)
noInversePointGivesDoubleNegatedDescent noPoint =
  noInfiniteSurvivorGivesDoubleNegatedDescent
    (noInversePointToNoInfiniteSurvivor noPoint)

------------------------------------------------------------------------
-- Exact logical extraction socket.
--
-- This is Markov's principle only for decidable predicates over Nat search.
-- It is typed as an explicit input rather than imported as an axiom.
------------------------------------------------------------------------

record NatSearchMarkov : Set₁ where
  field
    extract :
      {P : Nat → Set} →
      ((m : Nat) → Dec (P m)) →
      ¬ (¬ (Σ Nat P)) →
      Σ Nat P

open NatSearchMarkov public

strictDescentFromNoInfiniteWithMarkov :
  NatSearchMarkov →
  {x : Syracuse.PositiveNat} →
  NoInfiniteSurvivor x →
  Stop.StrictDescentWithin x
strictDescentFromNoInfiniteWithMarkov markov {x} noInfinite =
  extract
    markov
    (decDescentAt x)
    (noInfiniteSurvivorGivesDoubleNegatedDescent noInfinite)

strictDescentFromNoInversePointWithMarkov :
  NatSearchMarkov →
  {x : Syracuse.PositiveNat} →
  NoInverseSurvivorPoint x →
  Stop.StrictDescentWithin x
strictDescentFromNoInversePointWithMarkov markov {x} noPoint =
  extract
    markov
    (decDescentAt x)
    (noInversePointGivesDoubleNegatedDescent noPoint)

record NoInfiniteSurvivorSource : Set₁ where
  field
    excludesInfiniteSurvivor :
      (x : Syracuse.PositiveNat) →
      1 < Syracuse.toNat x →
      NoInfiniteSurvivor x

open NoInfiniteSurvivorSource public

noInfiniteSourceToLiteralStrictDescentWithMarkov :
  NatSearchMarkov →
  NoInfiniteSurvivorSource →
  Stop.LiteralStrictDescentSource
noInfiniteSourceToLiteralStrictDescentWithMarkov markov source = record
  { descend = λ x nontrivial →
      strictDescentFromNoInfiniteWithMarkov
        markov
        (excludesInfiniteSurvivor source x nontrivial)
  }

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record ConstructiveSurvivorExtractionBoundary : Set where
  constructor constructiveSurvivorExtractionBoundary
  field
    literalDescentPredicateDecidablePaid : Nat
    finitePrefixSearchPaid : Nat
    finiteBarrierExtractionPaid : Nat
    finiteBarrierToLiteralSourcePaid : Nat
    finiteBarrierToUniversalStoppingPaid : Nat
    strictDescentBuildsFiniteBarrierPaid : Nat
    finiteBarrierStrictDescentEquivalencePaid : Nat
    noInfiniteGivesDoubleNegatedDescentPaid : Nat
    noInversePointGivesDoubleNegatedDescentPaid : Nat
    explicitNatSearchMarkovSocketPaid : Nat
    markovConditionalExtractionCompilerPaid : Nat

    natSearchMarkovOwnedUnconditionally : Nat
    noInfiniteAutomaticallyConstructsDescent : Nat
    inverseLimitAbsenceAutomaticallyCreatesFiniteBarrier : Nat
    finiteDensityAutomaticallyCreatesFiniteBarrier : Nat

canonicalConstructiveSurvivorExtractionBoundary :
  ConstructiveSurvivorExtractionBoundary
canonicalConstructiveSurvivorExtractionBoundary =
  constructiveSurvivorExtractionBoundary
    1 1 1 1 1 1 1 1 1 1 1
    0 0 0 0
