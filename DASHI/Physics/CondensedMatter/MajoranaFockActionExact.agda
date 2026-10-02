module DASHI.Physics.CondensedMatter.MajoranaFockActionExact where

------------------------------------------------------------------------
-- Finite one-fermion Fock action for two Majoranas.
--
-- Exact basis action:
--   gamma1 |0> = |1>       gamma1 |1> = |0>
--   gamma2 |0> = i|1>      gamma2 |1> = -i|0>
--
-- Consequences proved by finite evaluation:
--   gamma1^2 = gamma2^2 = 1,
--   gamma1 gamma2 = - gamma2 gamma1.
--
-- We also encode f, f† and n=f†f on basis-or-zero vectors:
--   f|0>=0, f|1>=|0>
--   f†|0>=|1>, f†|1>=0
--   n|0>=0, n|1>=|1>, n^2=n.
--
-- This is a finite exact operator-action model, not a YbSb2 physical
-- realization claim.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

data Phase : Set where
  plusOne minusOne plusI minusI : Phase

phaseNegate : Phase → Phase
phaseNegate plusOne = minusOne
phaseNegate minusOne = plusOne
phaseNegate plusI = minusI
phaseNegate minusI = plusI

phaseMul : Phase → Phase → Phase
phaseMul plusOne p = p
phaseMul minusOne plusOne = minusOne
phaseMul minusOne minusOne = plusOne
phaseMul minusOne plusI = minusI
phaseMul minusOne minusI = plusI
phaseMul plusI plusOne = plusI
phaseMul plusI minusOne = minusI
phaseMul plusI plusI = minusOne
phaseMul plusI minusI = plusOne
phaseMul minusI plusOne = minusI
phaseMul minusI minusOne = plusI
phaseMul minusI plusI = plusOne
phaseMul minusI minusI = minusOne

data Occupation : Set where
  empty occupied : Occupation

record BasisState : Set where
  constructor basis
  field
    phase : Phase
    occupation : Occupation

open BasisState public

applyPhase : Phase → BasisState → BasisState
applyPhase p (basis q n) = basis (phaseMul p q) n

negateState : BasisState → BasisState
negateState = applyPhase minusOne

gamma1 : BasisState → BasisState
gamma1 (basis p empty) = basis p occupied
gamma1 (basis p occupied) = basis p empty

gamma2 : BasisState → BasisState
gamma2 (basis p empty) = basis (phaseMul p plusI) occupied
gamma2 (basis p occupied) = basis (phaseMul p minusI) empty

gamma1Square :
  (x : BasisState) →
  gamma1 (gamma1 x) ≡ x
gamma1Square (basis plusOne empty) = refl
gamma1Square (basis plusOne occupied) = refl
gamma1Square (basis minusOne empty) = refl
gamma1Square (basis minusOne occupied) = refl
gamma1Square (basis plusI empty) = refl
gamma1Square (basis plusI occupied) = refl
gamma1Square (basis minusI empty) = refl
gamma1Square (basis minusI occupied) = refl

gamma2Square :
  (x : BasisState) →
  gamma2 (gamma2 x) ≡ x
gamma2Square (basis plusOne empty) = refl
gamma2Square (basis plusOne occupied) = refl
gamma2Square (basis minusOne empty) = refl
gamma2Square (basis minusOne occupied) = refl
gamma2Square (basis plusI empty) = refl
gamma2Square (basis plusI occupied) = refl
gamma2Square (basis minusI empty) = refl
gamma2Square (basis minusI occupied) = refl

gamma12Anticommute :
  (x : BasisState) →
  gamma1 (gamma2 x)
  ≡ negateState (gamma2 (gamma1 x))
gamma12Anticommute (basis plusOne empty) = refl
gamma12Anticommute (basis plusOne occupied) = refl
gamma12Anticommute (basis minusOne empty) = refl
gamma12Anticommute (basis minusOne occupied) = refl
gamma12Anticommute (basis plusI empty) = refl
gamma12Anticommute (basis plusI occupied) = refl
gamma12Anticommute (basis minusI empty) = refl
gamma12Anticommute (basis minusI occupied) = refl

data FockVector : Set where
  zeroVector : FockVector
  nonzero : BasisState → FockVector

f : BasisState → FockVector
f (basis p empty) = zeroVector
f (basis p occupied) = nonzero (basis p empty)

fDagger : BasisState → FockVector
fDagger (basis p empty) = nonzero (basis p occupied)
fDagger (basis p occupied) = zeroVector

number : BasisState → FockVector
number (basis p empty) = zeroVector
number (basis p occupied) = nonzero (basis p occupied)

numberOnEmpty :
  (p : Phase) →
  number (basis p empty) ≡ zeroVector
numberOnEmpty p = refl

numberOnOccupied :
  (p : Phase) →
  number (basis p occupied)
  ≡ nonzero (basis p occupied)
numberOnOccupied p = refl

numberProjector :
  (x : BasisState) →
  number x ≡ zeroVector
  ⊎
  number x ≡ nonzero x
numberProjector (basis p empty) =
  Data.Sum.inj₁ refl
numberProjector (basis p occupied) =
  Data.Sum.inj₂ refl
