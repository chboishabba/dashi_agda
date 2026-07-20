module DASHI.Combinatorics.MonsterSSPFractranProjection where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Vec using (Vec; []; _∷_)

open import MonsterOntos
  using
    ( SSP
    ; p2; p3; p5; p7; p11
    ; p13; p17; p19; p23; p29
    ; p31; p41; p47; p59; p71
    )

------------------------------------------------------------------------
-- The fifteen supersingular primes are treated here as the compressed prime
-- support through which Monster-side structure is exposed to a prime-exponent
-- machine.  FRACTRAN is the execution substrate; SSP15 is the selected basis.
------------------------------------------------------------------------

SSP15ExponentState : Set
SSP15ExponentState = SSP → Nat

zeroSSP15State : SSP15ExponentState
zeroSSP15State _ = zero

------------------------------------------------------------------------
-- A Monster-side carrier is not defined by this module.  Instead, the exact
-- compression obligation is packaged: a chosen Monster object is projected to
-- the exponent/multiplicity carried by each of the fifteen SSP coordinates.
------------------------------------------------------------------------

record MonsterSSPCompression : Set₁ where
  field
    MonsterObject : Set

    project : MonsterObject → SSP15ExponentState

    EquivalentAtSSP15 : MonsterObject → MonsterObject → Set

    projection-sound :
      ∀ {left right} →
      project left ≡ project right →
      EquivalentAtSSP15 left right

    projection-complete :
      ∀ {left right} →
      EquivalentAtSSP15 left right →
      project left ≡ project right

open MonsterSSPCompression public

------------------------------------------------------------------------
-- Lossless reconstruction is stronger and requires a residual outside the
-- fifteen-prime projection.
------------------------------------------------------------------------

record MonsterSSPResidualCodec : Set₁ where
  field
    MonsterObject : Set
    Residual      : Set

    project  : MonsterObject → SSP15ExponentState
    residual : MonsterObject → Residual
    rebuild  : SSP15ExponentState → Residual → MonsterObject

    rebuild-project :
      ∀ object → rebuild (project object) (residual object) ≡ object

open MonsterSSPResidualCodec public

------------------------------------------------------------------------
-- FRACTRAN over the selected fifteen-prime basis.
--
-- Fractions are represented by numerator and denominator exponent functions.
-- Enabledness and subtraction remain explicit obligations rather than being
-- hidden in an integer divisibility implementation.
------------------------------------------------------------------------

record SSP15Fraction : Set where
  constructor ssp15Fraction
  field
    numerator   : SSP → Nat
    denominator : SSP → Nat

open SSP15Fraction public

record SSP15FractranMachine : Set₁ where
  field
    Program : Set

    instruction : Program → Nat → SSP15Fraction

    enabled : SSP15Fraction → SSP15ExponentState → Set
    apply   : SSP15Fraction → SSP15ExponentState → SSP15ExponentState

    guarded-update :
      ∀ fraction state →
      enabled fraction state →
      ∀ prime →
      apply fraction state prime + denominator fraction prime
        ≡ state prime + numerator fraction prime

    firstEnabledStep : Program → SSP15ExponentState → SSP15ExponentState

open SSP15FractranMachine public

------------------------------------------------------------------------
-- The actual cross-pollination theorem target.
--
-- Monster dynamics compress to FRACTRAN dynamics only when the SSP projection
-- commutes with the respective step operators.
------------------------------------------------------------------------

record MonsterSSPFractranSimulation
  (compression : MonsterSSPCompression)
  (machine : SSP15FractranMachine)
  : Set₁ where
  field
    program : Program machine

    monsterStep :
      MonsterObject compression → MonsterObject compression

    step-commutes :
      ∀ object →
      project compression (monsterStep object)
        ≡
      firstEnabledStep machine program (project compression object)

open MonsterSSPFractranSimulation public

------------------------------------------------------------------------
-- Support closure: if a larger prime-exponent state has no mass outside the
-- SSP basis, restriction to SSP15 is lossless.  The larger prime carrier and
-- membership witness remain parameters so this module does not pretend the
-- existing EV5 toy is already the full Monster/FRACTRAN machine.
------------------------------------------------------------------------

record PrimeSupportRestriction : Set₁ where
  field
    Prime : Set
    exponent : Prime → Nat
    embedSSP : SSP → Prime

    OutsideSSP : Prime → Set

    outside-zero :
      ∀ prime → OutsideSSP prime → exponent prime ≡ zero

    restricted : SSP15ExponentState
    restricted ssp = exponent (embedSSP ssp)

open PrimeSupportRestriction public

------------------------------------------------------------------------
-- Honest authority boundary.
------------------------------------------------------------------------

record MonsterSSPFractranBoundary : Set₁ where
  field
    monsterCarrierSpecified          : Set
    sspProjectionDerived             : Set
    projectionMatchesMonsterInvariant : Set
    fractranStepSimulationProved     : Set
    outsidePrimeResidualSpecified    : Set

MonsterSSPFractranTarget : Set₁
MonsterSSPFractranTarget = MonsterSSPFractranBoundary
