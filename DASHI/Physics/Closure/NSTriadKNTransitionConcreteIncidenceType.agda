module DASHI.Physics.Closure.NSTriadKNTransitionConcreteIncidenceType where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin using (Fin)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_)

open import DASHI.Physics.Closure.NSTriadKNTransitionPrimitiveEstimates
  using ( TransitionClass
        ; transitionRowCountBound
        ; transitionColumnCountBound
        )

------------------------------------------------------------------------
-- Concrete transition triad incidence and bounded parameter types.
--
-- This mirrors the adversarial concrete incidence lane. The transition
-- profile uses the requested four-way class split and packages bounded row
-- and column parameters into a finite incidence type that downstream row and
-- column witnesses can depend on canonically.

TransitionHead : TransitionClass -> Nat -> Set
TransitionHead c N = Fin (transitionRowCountBound c N)

TransitionTail : TransitionClass -> Nat -> Set
TransitionTail c N = Fin (transitionColumnCountBound c N)

transitionFiberConstant : TransitionClass -> Nat
transitionFiberConstant _ = 1

record TransitionTriadIncidence (c : TransitionClass) (N : Nat) : Set where
  constructor mkTransitionTriadIncidence
  field
    headParam : TransitionHead c N
    tailParam : TransitionTail c N
    residueTag : Fin (transitionFiberConstant c)

open TransitionTriadIncidence public

TransitionEncoding : TransitionClass -> Nat -> Set
TransitionEncoding c N = TransitionHead c N × TransitionTail c N

enc : {c : TransitionClass} {N : Nat} ->
      TransitionTriadIncidence c N -> TransitionEncoding c N
enc τ = headParam τ , tailParam τ

transitionFiberInjectivity :
  {c : TransitionClass} {N : Nat} ->
  (τ₁ τ₂ : TransitionTriadIncidence c N) ->
  headParam τ₁ ≡ headParam τ₂ ->
  tailParam τ₁ ≡ tailParam τ₂ ->
  residueTag τ₁ ≡ residueTag τ₂ ->
  τ₁ ≡ τ₂
transitionFiberInjectivity
  (mkTransitionTriadIncidence h t r)
  (mkTransitionTriadIncidence .h .t .r)
  refl refl refl = refl

transitionConcreteHeadBound :
  (c : TransitionClass) (N : Nat) ->
  transitionRowCountBound c N ≤ transitionRowCountBound c N
transitionConcreteHeadBound _ _ = ≤-refl

transitionConcreteTailBound :
  (c : TransitionClass) (N : Nat) ->
  transitionColumnCountBound c N ≤ transitionColumnCountBound c N
transitionConcreteTailBound _ _ = ≤-refl

transitionFiberSizeBound :
  {c : TransitionClass} {N : Nat} ->
  transitionFiberConstant c ≤ transitionFiberConstant c
transitionFiberSizeBound = ≤-refl

record TransitionConcreteIncidenceStatus : Set where
  constructor mkTransitionConcreteIncidenceStatus
  field
    rowParameterBounded : Bool
    columnParameterBounded : Bool
    residueFiberBounded : Bool
    abstractWiringComplete : Bool

open TransitionConcreteIncidenceStatus public

currentTransitionConcreteIncidenceStatus :
  TransitionConcreteIncidenceStatus
currentTransitionConcreteIncidenceStatus =
  mkTransitionConcreteIncidenceStatus
    false
    false
    false
    false
