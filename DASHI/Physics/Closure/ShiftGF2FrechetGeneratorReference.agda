module DASHI.Physics.Closure.ShiftGF2FrechetGeneratorReference where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.FixedPointAnalyticRGTargets as Targets
open import DASHI.Physics.Closure.ShiftGF2BanachTangentReference as Banach

------------------------------------------------------------------------
-- Exact Frechet-style reference over the finite discrete GF(2) tangent.
--
-- The nonlinear map is the one-step absorbing map F(x)=0.  Its derivative at
-- the fixed point is the zero linear map, so the remainder vanishes exactly.
-- The Nat-indexed flow is identity at time zero and zero afterwards.
-- This gives a genuine discrete semigroup and exact derivative theorem over the
-- finite valued field, but not a real-time C0 analytic semigroup.

absorbingMap : Bool → Bool
absorbingMap x = false

frechetDerivative : Bool → Bool
frechetDerivative h = false

generator : Bool → Bool
generator h = false

flow : Nat → Bool → Bool
flow zero x = x
flow (suc n) x = false

flowZero : (x : Bool) → flow zero x ≡ x
flowZero x = refl

flowSemigroup :
  (m n : Nat) →
  (x : Bool) →
  flow (m + n) x ≡ flow n (flow m x)
flowSemigroup zero n x = refl
flowSemigroup (suc m) zero x = refl
flowSemigroup (suc m) (suc n) x = refl

derivativeAdditive :
  (x y : Bool) →
  frechetDerivative (x Banach.⊕₂ y)
    ≡
  frechetDerivative x Banach.⊕₂ frechetDerivative y
derivativeAdditive x y = refl

derivativeHomogeneous :
  (a x : Bool) →
  frechetDerivative (a Banach.⊗₂ x)
    ≡
  a Banach.⊗₂ frechetDerivative x
derivativeHomogeneous a x = refl

ExactFrechetRemainderZero : Set
ExactFrechetRemainderZero =
  (x h : Bool) →
  absorbingMap (x Banach.⊕₂ h)
    Banach.⊕₂
  (absorbingMap x Banach.⊕₂ frechetDerivative h)
    ≡ false

exactFrechetRemainderZero : ExactFrechetRemainderZero
exactFrechetRemainderZero x h = refl

GeneratorLimitLaw : Set
GeneratorLimitLaw =
  (x : Bool) →
  flow (suc zero) x ≡ generator x

generatorLimitLaw : GeneratorLimitLaw
generatorLimitLaw x = refl

StrongContinuityDiscrete : Set
StrongContinuityDiscrete =
  (x : Bool) →
  flow zero x ≡ x

strongContinuityDiscrete : StrongContinuityDiscrete
strongContinuityDiscrete = flowZero

shiftGF2FrechetLinearizedSemigroup :
  Targets.FrechetLinearizedSemigroup
    Bool Bool Nat Banach.shiftGF2AdditiveNormedTangent
shiftGF2FrechetLinearizedSemigroup =
  record
    { zeroTime = zero
    ; _+time_ = _+_
    ; flow = flow
    ; derivative = frechetDerivative
    ; generator = generator
    ; zeroTimeLaw = flowZero
    ; semigroupLaw = flowSemigroup
    ; derivativeAdditive = derivativeAdditive
    ; FrechetRemainderControlled = ExactFrechetRemainderZero
    ; GeneratorLimitExists = GeneratorLimitLaw
    ; StronglyContinuous = StrongContinuityDiscrete
    }

record ShiftGF2FrechetGeneratorReference : Setω where
  field
    banachTangent : Banach.ShiftGF2BanachTangentReference
    linearizedSemigroup :
      Targets.FrechetLinearizedSemigroup
        Bool Bool Nat Banach.shiftGF2AdditiveNormedTangent
    derivativeLinear :
      (x y : Bool) →
      frechetDerivative (x Banach.⊕₂ y)
        ≡
      frechetDerivative x Banach.⊕₂ frechetDerivative y
    derivativeScalar :
      (a x : Bool) →
      frechetDerivative (a Banach.⊗₂ x)
        ≡
      a Banach.⊗₂ frechetDerivative x
    remainderExactlyZero : ExactFrechetRemainderZero
    generatorOneStep : GeneratorLimitLaw
    strongContinuityAtZero : StrongContinuityDiscrete
    nonClaimBoundary : List String

open ShiftGF2FrechetGeneratorReference public

canonicalShiftGF2FrechetGeneratorReference :
  ShiftGF2FrechetGeneratorReference
canonicalShiftGF2FrechetGeneratorReference =
  record
    { banachTangent = Banach.canonicalShiftGF2BanachTangentReference
    ; linearizedSemigroup = shiftGF2FrechetLinearizedSemigroup
    ; derivativeLinear = derivativeAdditive
    ; derivativeScalar = derivativeHomogeneous
    ; remainderExactlyZero = exactFrechetRemainderZero
    ; generatorOneStep = generatorLimitLaw
    ; strongContinuityAtZero = strongContinuityDiscrete
    ; nonClaimBoundary =
        "ShiftGF2FrechetGeneratorReference has an exact zero remainder on a finite complete valued-field tangent"
        ∷ "the generator is the exact one-step discrete generator of the absorbing GF(2) semigroup"
        ∷ "time is Nat and strong continuity is the discrete zero-time law"
        ∷ "No real-time C0 semigroup, sectorial generator, resolvent estimate, or physical Frechet derivative is claimed"
        ∷ []
    }
