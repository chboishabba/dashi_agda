module DASHI.Physics.Closure.NSTriadKNLuoFiniteBonyFourClassAccountingExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Jean-Michel Bony; Hajer Bahouri; Jean-Yves Chemin;
-- Raphael Danchin.
-- Bony title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- Annales scientifiques de l'Ecole Normale Superieure 14 (1981), 209--246.
-- DOI: 10.24033/asens.1404.
--
-- Bahouri--Chemin--Danchin title:
-- "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Keep the four terminal-window interaction classes separate until their
-- estimates have been proved:
--
--   low--high,
--   high--low,
--   comparable triads,
--   high--high to low backscatter.
--
-- The first theorem is a literal finite partition of a tagged interaction
-- list.  The second theorem assembles four classwise estimates.  Every
-- analytic bound remains an explicit field of the input record, so no
-- continuum estimate is hidden inside the bookkeeping theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

data InteractionClass : Set where
  lowHighClass highLowClass comparableClass highHighToLowClass :
    InteractionClass

record TaggedInteraction : Set where
  constructor tagged-interaction
  field
    interactionClass : InteractionClass
    interactionValue : ℚ

open TaggedInteraction public

allInteractionSum : List TaggedInteraction → ℚ
allInteractionSum [] = 0ℚ
allInteractionSum (interaction ∷ interactions) =
  interactionValue interaction + allInteractionSum interactions

lowHighSum : List TaggedInteraction → ℚ
lowHighSum [] = 0ℚ
lowHighSum
  (tagged-interaction lowHighClass value ∷ interactions) =
  value + lowHighSum interactions
lowHighSum (_ ∷ interactions) = lowHighSum interactions

highLowSum : List TaggedInteraction → ℚ
highLowSum [] = 0ℚ
highLowSum
  (tagged-interaction highLowClass value ∷ interactions) =
  value + highLowSum interactions
highLowSum (_ ∷ interactions) = highLowSum interactions

comparableSum : List TaggedInteraction → ℚ
comparableSum [] = 0ℚ
comparableSum
  (tagged-interaction comparableClass value ∷ interactions) =
  value + comparableSum interactions
comparableSum (_ ∷ interactions) = comparableSum interactions

highHighToLowSum : List TaggedInteraction → ℚ
highHighToLowSum [] = 0ℚ
highHighToLowSum
  (tagged-interaction highHighToLowClass value ∷ interactions) =
  value + highHighToLowSum interactions
highHighToLowSum (_ ∷ interactions) = highHighToLowSum interactions

fourClassPartitionExact :
  (interactions : List TaggedInteraction) →
  allInteractionSum interactions
  ≡ lowHighSum interactions
    + highLowSum interactions
    + comparableSum interactions
    + highHighToLowSum interactions
fourClassPartitionExact [] = solve []
fourClassPartitionExact
  (tagged-interaction lowHighClass value ∷ interactions)
  rewrite fourClassPartitionExact interactions =
  solve
    ( value
    ∷ lowHighSum interactions
    ∷ highLowSum interactions
    ∷ comparableSum interactions
    ∷ highHighToLowSum interactions
    ∷ [])
fourClassPartitionExact
  (tagged-interaction highLowClass value ∷ interactions)
  rewrite fourClassPartitionExact interactions =
  solve
    ( value
    ∷ lowHighSum interactions
    ∷ highLowSum interactions
    ∷ comparableSum interactions
    ∷ highHighToLowSum interactions
    ∷ [])
fourClassPartitionExact
  (tagged-interaction comparableClass value ∷ interactions)
  rewrite fourClassPartitionExact interactions =
  solve
    ( value
    ∷ lowHighSum interactions
    ∷ highLowSum interactions
    ∷ comparableSum interactions
    ∷ highHighToLowSum interactions
    ∷ [])
fourClassPartitionExact
  (tagged-interaction highHighToLowClass value ∷ interactions)
  rewrite fourClassPartitionExact interactions =
  solve
    ( value
    ∷ lowHighSum interactions
    ∷ highLowSum interactions
    ∷ comparableSum interactions
    ∷ highHighToLowSum interactions
    ∷ [])

record FourClassTerminalBudget : Set where
  constructor four-class-terminal-budget
  field
    lowHigh highLow comparable highHighToLow : ℚ
    lowHighCoefficient highLowCoefficient : ℚ
    comparableCoefficient highHighToLowCoefficient : ℚ
    tailRoot shellEnergy : ℚ

    lowHighBound :
      lowHigh ≤ lowHighCoefficient * tailRoot * shellEnergy
    highLowBound :
      highLow ≤ highLowCoefficient * tailRoot * shellEnergy
    comparableBound :
      comparable ≤ comparableCoefficient * tailRoot * shellEnergy
    highHighToLowBound :
      highHighToLow
      ≤ highHighToLowCoefficient * tailRoot * shellEnergy

open FourClassTerminalBudget public

totalInteraction : FourClassTerminalBudget → ℚ
totalInteraction budget =
  lowHigh budget
  + highLow budget
  + comparable budget
  + highHighToLow budget

coefficientSum : FourClassTerminalBudget → ℚ
coefficientSum budget =
  lowHighCoefficient budget
  + highLowCoefficient budget
  + comparableCoefficient budget
  + highHighToLowCoefficient budget

fourClassTerminalAssembly :
  (budget : FourClassTerminalBudget) →
  totalInteraction budget
  ≤ coefficientSum budget * tailRoot budget * shellEnergy budget
fourClassTerminalAssembly budget =
  let
    summed :
      lowHigh budget
        + highLow budget
        + comparable budget
        + highHighToLow budget
      ≤ (lowHighCoefficient budget * tailRoot budget * shellEnergy budget)
        + (highLowCoefficient budget * tailRoot budget * shellEnergy budget)
        + (comparableCoefficient budget * tailRoot budget * shellEnergy budget)
        + (highHighToLowCoefficient budget
            * tailRoot budget * shellEnergy budget)
    summed =
      ℚₚ.+-mono-≤
        (ℚₚ.+-mono-≤
          (ℚₚ.+-mono-≤
            (lowHighBound budget)
            (highLowBound budget))
          (comparableBound budget))
        (highHighToLowBound budget)

    targetMeaning :
      (lowHighCoefficient budget * tailRoot budget * shellEnergy budget)
        + (highLowCoefficient budget * tailRoot budget * shellEnergy budget)
        + (comparableCoefficient budget * tailRoot budget * shellEnergy budget)
        + (highHighToLowCoefficient budget
            * tailRoot budget * shellEnergy budget)
      ≡ coefficientSum budget * tailRoot budget * shellEnergy budget
    targetMeaning =
      solve
        ( lowHighCoefficient budget
        ∷ highLowCoefficient budget
        ∷ comparableCoefficient budget
        ∷ highHighToLowCoefficient budget
        ∷ tailRoot budget
        ∷ shellEnergy budget
        ∷ [])
  in
  subst
    (λ upper → totalInteraction budget ≤ upper)
    targetMeaning
    summed
