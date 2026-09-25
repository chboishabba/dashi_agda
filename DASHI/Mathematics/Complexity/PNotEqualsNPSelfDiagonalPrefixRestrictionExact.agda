module DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalPrefixRestrictionExact where

------------------------------------------------------------------------
-- LITERAL PREFIX RESTRICTION FOR THE ROOT-SCOPED P9 AUTOMATON
--
-- Existing:
--
--   PNotEqualsNPSelfDiagonalRestrictionFamilyExact
--
-- represents reachable Shannon descendants by RestrictionDerivation.
--
-- This owner exposes the same family on literal partial assignments:
--
--   restrictPrefix :
--     Vec Bool p ->
--     BooleanFormula (p + r) ->
--     BooleanFormula r.
--
-- Main theorems:
--
--   * one prefix bit is exactly one restrictHead step;
--   * every literal prefix restriction has a RestrictionDerivation;
--   * quotient classification of that descendant is exactly the fold of the
--     quotient transition function over the prefix.
--
-- This is the concrete q(a) carrier required by the resource-closing
-- self-diagonal quotient programme.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Fin.Base using (Fin)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient

------------------------------------------------------------------------
-- Literal prefix restriction.
------------------------------------------------------------------------

restrictPrefix :
  ∀ {prefixLength remaining : Nat} ->
  Vec Bool prefixLength ->
  SAT.BooleanFormula (prefixLength + remaining) ->
  SAT.BooleanFormula remaining
restrictPrefix {zero} [] formula =
  formula
restrictPrefix {suc prefixLength}
    (bit ∷ bits)
    formula =
  restrictPrefix
    bits
    (SAT.restrictHead bit formula)

restrictPrefixCons :
  ∀ {prefixLength remaining : Nat}
    (bit : Bool)
    (bits : Vec Bool prefixLength)
    (formula :
      SAT.BooleanFormula
        (suc prefixLength + remaining)) ->
  restrictPrefix
    (bit ∷ bits)
    formula
  ≡
  restrictPrefix
    bits
    (SAT.restrictHead bit formula)
restrictPrefixCons bit bits formula =
  refl

------------------------------------------------------------------------
-- Extend any existing restriction derivation along a literal prefix.
------------------------------------------------------------------------

prefixRestrictionDerivationFrom :
  ∀ {rootVariables prefixLength remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {current :
      SAT.BooleanFormula
        (prefixLength + remaining)} ->
  Family.RestrictionDerivation
    root
    current ->
  (prefix : Vec Bool prefixLength) ->
  Family.RestrictionDerivation
    root
    (restrictPrefix prefix current)
prefixRestrictionDerivationFrom
    derivation
    [] =
  derivation
prefixRestrictionDerivationFrom
    derivation
    (false ∷ bits) =
  prefixRestrictionDerivationFrom
    (Family.restrictionFalse derivation)
    bits
prefixRestrictionDerivationFrom
    derivation
    (true ∷ bits) =
  prefixRestrictionDerivationFrom
    (Family.restrictionTrue derivation)
    bits

prefixRestrictionDerivation :
  ∀ {prefixLength remaining : Nat}
    (prefix : Vec Bool prefixLength)
    (root :
      SAT.BooleanFormula
        (prefixLength + remaining)) ->
  Family.RestrictionDerivation
    root
    (restrictPrefix prefix root)
prefixRestrictionDerivation
    prefix
    root =
  prefixRestrictionDerivationFrom
    Family.restrictionRoot
    prefix

------------------------------------------------------------------------
-- Quotient transition fold on a literal prefix.
------------------------------------------------------------------------

foldQuotientState :
  ∀ {rootVariables prefixLength : Nat}
    {root : SAT.BooleanFormula rootVariables} ->
  Quotient.RestrictionSemanticQuotient root ->
  Vec Bool prefixLength ->
  Fin (Quotient.stateCount quotient) ->
  Fin (Quotient.stateCount quotient)
foldQuotientState quotient [] state =
  state
foldQuotientState quotient (bit ∷ bits) state =
  foldQuotientState
    quotient
    bits
    (Quotient.step quotient state bit)

------------------------------------------------------------------------
-- Main automaton theorem.
--
-- Classification after restricting by prefix equals transition-fold from the
-- current quotient state.
------------------------------------------------------------------------

prefixClassificationIsTransitionFoldFrom :
  ∀ {rootVariables prefixLength remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {current :
      SAT.BooleanFormula
        (prefixLength + remaining)}
    (quotient :
      Quotient.RestrictionSemanticQuotient root)
    (derivation :
      Family.RestrictionDerivation
        root
        current)
    (prefix : Vec Bool prefixLength) ->
  Quotient.classify
    quotient
    (prefixRestrictionDerivationFrom
      derivation
      prefix)
  ≡
  foldQuotientState
    quotient
    prefix
    (Quotient.classify
      quotient
      derivation)
prefixClassificationIsTransitionFoldFrom
    quotient
    derivation
    [] =
  refl
prefixClassificationIsTransitionFoldFrom
    quotient
    derivation
    (false ∷ bits) =
  trans
    (prefixClassificationIsTransitionFoldFrom
      quotient
      (Family.restrictionFalse derivation)
      bits)
    (foldCongruence
      (Quotient.falseStepCompatible
        quotient
        derivation))
  where
    foldCongruence :
      ∀ {left right :
          Fin (Quotient.stateCount quotient)} ->
      left ≡ right ->
      foldQuotientState
        quotient
        bits
        left
      ≡
      foldQuotientState
        quotient
        bits
        right
    foldCongruence refl =
      refl
prefixClassificationIsTransitionFoldFrom
    quotient
    derivation
    (true ∷ bits) =
  trans
    (prefixClassificationIsTransitionFoldFrom
      quotient
      (Family.restrictionTrue derivation)
      bits)
    (foldCongruence
      (Quotient.trueStepCompatible
        quotient
        derivation))
  where
    foldCongruence :
      ∀ {left right :
          Fin (Quotient.stateCount quotient)} ->
      left ≡ right ->
      foldQuotientState
        quotient
        bits
        left
      ≡
      foldQuotientState
        quotient
        bits
        right
    foldCongruence refl =
      refl

prefixClassificationIsTransitionFold :
  ∀ {prefixLength remaining : Nat}
    (root :
      SAT.BooleanFormula
        (prefixLength + remaining))
    (quotient :
      Quotient.RestrictionSemanticQuotient root)
    (prefix : Vec Bool prefixLength) ->
  Quotient.classify
    quotient
    (prefixRestrictionDerivation
      prefix
      root)
  ≡
  foldQuotientState
    quotient
    prefix
    (Quotient.classify
      quotient
      Family.restrictionRoot)
prefixClassificationIsTransitionFold
    root
    quotient
    prefix =
  prefixClassificationIsTransitionFoldFrom
    quotient
    Family.restrictionRoot
    prefix

------------------------------------------------------------------------
-- Concrete P9 interpretation.
--
-- For one root formula, the abstract derivation-indexed quotient is exactly a
-- finite automaton on partial assignments:
--
--   q([])       = q_root
--   q(b :: rest)= fold(rest, step(q_root,b)).
--
-- A future self-diagonal construction can therefore reason directly about
-- prefix assignments and reachable quotient states without manufacturing
-- derivation proofs by hand.
------------------------------------------------------------------------
