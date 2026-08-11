module DASHI.Physics.Closure.NSTriadKNHHBadSchurInverseScaleRound36Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: P. K. Mitter.
-- Title: "The Exact Renormalization Group".
-- Persistent identifier: 10.48550/arXiv.math-ph/0505008.
--
-- Authors: Wojciech Dybalski; Alexander Stottmeister; Yoh Tanimoto.
-- Title: "The Bałaban variational problem in the non-linear sigma model".
-- Persistent identifier: 10.48550/arXiv.2403.09800.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- Round 35 proved that the HH-bad owner needs one inverse dyadic power and
-- that a scale-free gain cannot absorb the raw +1 shell power.  This module
-- tests the Schur/Feshbach route suggested by the fibre analysis rather than
-- merely restating that obstruction.
--
-- If a fine block has parabolic scale
--
--   D ~ nu lambda^2,
--
-- then its inverse has
--
--   D^-1 ~ nu^-1 lambda^-2.
--
-- The Schur correction B D^-1 C therefore has exactly one inverse shell power
-- when exactly one of B,C contributes one derivative, while two derivative
-- couplings cancel both inverse shell powers and leave a scale-free shell
-- degree.  This is the precise scale test required before trying to identify
-- the actual HH-bad operator blocks.
--
-- Viscosity also needs a signed exponent.  Round 35's ScaleValuation records
-- only nonnegative viscosity degree, so a separate four-coordinate signed
-- valuation is used here rather than pretending that nu^-1 fits that type.
-- No physical Schur block realization is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_+_)
open import Data.Product using (_×_; _,_)

record SignedSchurScale : Set where
  constructor signed-schur-scale
  field
    shellGrowth : Nat
    shellDecay : Nat
    viscosityGrowth : Nat
    viscosityDecay : Nat

open SignedSchurScale public

_⊗s_ : SignedSchurScale → SignedSchurScale → SignedSchurScale
left ⊗s right =
  signed-schur-scale
    (shellGrowth left + shellGrowth right)
    (shellDecay left + shellDecay right)
    (viscosityGrowth left + viscosityGrowth right)
    (viscosityDecay left + viscosityDecay right)

infixr 6 _⊗s_

SameSchurScale : SignedSchurScale → SignedSchurScale → Set
SameSchurScale left right =
  (shellGrowth left + shellDecay right
    ≡ shellGrowth right + shellDecay left)
  ×
  (viscosityGrowth left + viscosityDecay right
    ≡ viscosityGrowth right + viscosityDecay left)

identityScale : SignedSchurScale
identityScale = signed-schur-scale 0 0 0 0

fineParabolicBlockScale : SignedSchurScale
fineParabolicBlockScale = signed-schur-scale 2 0 1 0

fineParabolicInverseScale : SignedSchurScale
fineParabolicInverseScale = signed-schur-scale 0 2 0 1

boundedCouplingScale : SignedSchurScale
boundedCouplingScale = identityScale

oneDerivativeCouplingScale : SignedSchurScale
oneDerivativeCouplingScale = signed-schur-scale 1 0 0 0

inverseShellSchurScale : SignedSchurScale
inverseShellSchurScale = signed-schur-scale 0 1 0 1

scaleFreeSchurScale : SignedSchurScale
scaleFreeSchurScale = signed-schur-scale 0 0 0 1

fineBlockInverseCancelsExactly :
  SameSchurScale
    (fineParabolicBlockScale ⊗s fineParabolicInverseScale)
    identityScale
fineBlockInverseCancelsExactly = refl , refl

leftDerivativeSchurHasInverseShellScale :
  SameSchurScale
    (oneDerivativeCouplingScale
      ⊗s fineParabolicInverseScale
      ⊗s boundedCouplingScale)
    inverseShellSchurScale
leftDerivativeSchurHasInverseShellScale = refl , refl

rightDerivativeSchurHasInverseShellScale :
  SameSchurScale
    (boundedCouplingScale
      ⊗s fineParabolicInverseScale
      ⊗s oneDerivativeCouplingScale)
    inverseShellSchurScale
rightDerivativeSchurHasInverseShellScale = refl , refl

twoDerivativeSchurIsScaleFree :
  SameSchurScale
    (oneDerivativeCouplingScale
      ⊗s fineParabolicInverseScale
      ⊗s oneDerivativeCouplingScale)
    scaleFreeSchurScale
twoDerivativeSchurIsScaleFree = refl , refl

twoDerivativeSchurCannotHaveInverseShellScale :
  SameSchurScale
    (oneDerivativeCouplingScale
      ⊗s fineParabolicInverseScale
      ⊗s oneDerivativeCouplingScale)
    inverseShellSchurScale
  → ⊥
twoDerivativeSchurCannotHaveInverseShellScale (() , viscosityMatch)

record HHBadSchurScalePattern : Set where
  constructor hhbad-schur-scale-pattern
  field
    leftCoupling : SignedSchurScale
    fineInverse : SignedSchurScale
    rightCoupling : SignedSchurScale
    resultingScale : SignedSchurScale

    leftExact : leftCoupling ≡ oneDerivativeCouplingScale
    inverseExact : fineInverse ≡ fineParabolicInverseScale
    rightExact : rightCoupling ≡ boundedCouplingScale
    resultExact : resultingScale ≡ inverseShellSchurScale

open HHBadSchurScalePattern public

canonicalLeftDerivativeHHBadSchurPattern : HHBadSchurScalePattern
canonicalLeftDerivativeHHBadSchurPattern =
  hhbad-schur-scale-pattern
    oneDerivativeCouplingScale
    fineParabolicInverseScale
    boundedCouplingScale
    inverseShellSchurScale
    refl refl refl refl

hhBadSchurPatternProducesRequiredInverseScale :
  (pattern : HHBadSchurScalePattern) →
  SameSchurScale
    (leftCoupling pattern ⊗s fineInverse pattern ⊗s rightCoupling pattern)
    (resultingScale pattern)
hhBadSchurPatternProducesRequiredInverseScale pattern
  rewrite leftExact pattern
        | inverseExact pattern
        | rightExact pattern
        | resultExact pattern
  = leftDerivativeSchurHasInverseShellScale

schurOneDerivativeInverseScaleClosed : Bool
schurOneDerivativeInverseScaleClosed = true

twoDerivativeSchurNoGoClosed : Bool
twoDerivativeSchurNoGoClosed = true

physicalHHBadSchurBlockRealizationConstructed : Bool
physicalHHBadSchurBlockRealizationConstructed = false

schurOneDerivativeInverseScaleClosedIsTrue :
  schurOneDerivativeInverseScaleClosed ≡ true
schurOneDerivativeInverseScaleClosedIsTrue = refl

twoDerivativeSchurNoGoClosedIsTrue :
  twoDerivativeSchurNoGoClosed ≡ true
twoDerivativeSchurNoGoClosedIsTrue = refl

physicalHHBadSchurBlockRealizationConstructedIsFalse :
  physicalHHBadSchurBlockRealizationConstructed ≡ false
physicalHHBadSchurBlockRealizationConstructedIsFalse = refl
