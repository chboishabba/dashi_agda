module DASHI.Physics.Closure.NSTriadKNAdversarialConcreteIncidenceType where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin using (Fin)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_)

open import DASHI.Physics.Closure.NSTriadKNAdversarialPrimitiveEstimates
  using ( AdversarialClass
        ; adversarialRowCountBound
        ; adversarialColumnCountBound
        )

------------------------------------------------------------------------
-- Concrete adversarial triad incidence and bounded parameter types.
--
-- This mirrors the forced-tail concrete incidence pattern at a lighter
-- level: the parameter spaces are bounded by the classwise count formulas,
-- and the remaining residue freedom is kept finite by construction.
--
-- For the first adversarial theorem we only need the row lane, but the
-- incidence type already exposes both row- and column-oriented bounded
-- parameters so later column work can reuse the same model.

AdversarialHead : AdversarialClass -> Nat -> Set
AdversarialHead c N = Fin (adversarialRowCountBound c N)

AdversarialTail : AdversarialClass -> Nat -> Set
AdversarialTail c N = Fin (adversarialColumnCountBound c N)

adversarialFiberConstant : AdversarialClass -> Nat
adversarialFiberConstant _ = 1

record AdversarialTriadIncidence (c : AdversarialClass) (N : Nat) : Set where
  constructor mkAdversarialTriadIncidence
  field
    headParam : AdversarialHead c N
    tailParam : AdversarialTail c N
    residueTag : Fin (adversarialFiberConstant c)

open AdversarialTriadIncidence public

AdversarialEncoding : AdversarialClass -> Nat -> Set
AdversarialEncoding c N = AdversarialHead c N × AdversarialTail c N

enc : {c : AdversarialClass} {N : Nat} ->
      AdversarialTriadIncidence c N -> AdversarialEncoding c N
enc τ = headParam τ , tailParam τ

adversarialFiberInjectivity :
  {c : AdversarialClass} {N : Nat} ->
  (τ₁ τ₂ : AdversarialTriadIncidence c N) ->
  headParam τ₁ ≡ headParam τ₂ ->
  tailParam τ₁ ≡ tailParam τ₂ ->
  residueTag τ₁ ≡ residueTag τ₂ ->
  τ₁ ≡ τ₂
adversarialFiberInjectivity
  (mkAdversarialTriadIncidence h t r)
  (mkAdversarialTriadIncidence .h .t .r)
  refl refl refl = refl

adversarialConcreteHeadBound :
  (c : AdversarialClass) (N : Nat) ->
  adversarialRowCountBound c N ≤ adversarialRowCountBound c N
adversarialConcreteHeadBound _ _ = ≤-refl

adversarialConcreteTailBound :
  (c : AdversarialClass) (N : Nat) ->
  adversarialColumnCountBound c N ≤ adversarialColumnCountBound c N
adversarialConcreteTailBound _ _ = ≤-refl

adversarialFiberSizeBound :
  {c : AdversarialClass} {N : Nat} ->
  adversarialFiberConstant c ≤ adversarialFiberConstant c
adversarialFiberSizeBound = ≤-refl

record AdversarialConcreteIncidenceStatus : Set where
  constructor mkAdversarialConcreteIncidenceStatus
  field
    rowParameterBounded : Bool
    columnParameterBounded : Bool
    residueFiberBounded : Bool
    abstractWiringComplete : Bool

open AdversarialConcreteIncidenceStatus public

currentAdversarialConcreteIncidenceStatus :
  AdversarialConcreteIncidenceStatus
currentAdversarialConcreteIncidenceStatus =
  mkAdversarialConcreteIncidenceStatus
    false
    false
    false
    false
