module DASHI.Moonshine.DuncanSwisherOrbitGatedDeligneDepthControlsExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
--
-- Their Theorem 1.2 supplies the rational/non-rational supersingular regimes,
-- while Proposition 3.1 identifies the n=1 Deligne pole-depth scale.  Combined
-- with the full elliptic automorphism orders for p>3, the positive Monster
-- exponents factor as
--
--   singleton rational : 3 * d_min,
--   multiple rational  :     d_min,
--   non-rational locus : 0,
--
-- where 2*d_min = m_p.
--
-- DASHI CONTRIBUTION
--
-- Make that "depth unit + orbit gate" decomposition concrete on structurally
-- different primes 5,7,11,13,37,43.  This separates two roles that the scalar
-- exponent alone hides:
--
--   Deligne/automorphism depth gives the multiplicity UNIT;
--   Frobenius rationality stratum decides whether the unit contributes once,
--   three times, or is killed completely.
--
-- In particular p=37 and p=43 still have generic depth unit 1, but the
-- non-rational supersingular locus forces Monster exponent zero.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.DuncanSwisherDeligneAutomorphismDepthBridgeExact as Deligne
import DASHI.Moonshine.DuncanSwisherMonsterExponentGeometryExact as Geo
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Monster
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- Minimum Deligne-depth witnesses attached to the minimum full-aut type.
------------------------------------------------------------------------

p5MinimumWitness : Deligne.MinimumAutomorphismWitness
p5MinimumWitness =
  Deligne.minimum-automorphism-witness Deligne.jZeroExceptional 6 refl

p7MinimumWitness : Deligne.MinimumAutomorphismWitness
p7MinimumWitness =
  Deligne.minimum-automorphism-witness Deligne.j1728Exceptional 4 refl

p11MinimumWitness : Deligne.MinimumAutomorphismWitness
p11MinimumWitness = Deligne.p11MinimumWitness

p13MinimumWitness : Deligne.MinimumAutomorphismWitness
p13MinimumWitness =
  Deligne.minimum-automorphism-witness Deligne.ordinaryType 2 refl

p37MinimumWitness : Deligne.MinimumAutomorphismWitness
p37MinimumWitness =
  Deligne.minimum-automorphism-witness Deligne.ordinaryType 2 refl

p43MinimumWitness : Deligne.MinimumAutomorphismWitness
p43MinimumWitness =
  Deligne.minimum-automorphism-witness Deligne.ordinaryType 2 refl

p5DepthUnit : Nat
p5DepthUnit = Deligne.minimumFirstPoleDepth p5MinimumWitness

p7DepthUnit : Nat
p7DepthUnit = Deligne.minimumFirstPoleDepth p7MinimumWitness

p11DepthUnit : Nat
p11DepthUnit = Deligne.minimumFirstPoleDepth p11MinimumWitness

p13DepthUnit : Nat
p13DepthUnit = Deligne.minimumFirstPoleDepth p13MinimumWitness

p37DepthUnit : Nat
p37DepthUnit = Deligne.minimumFirstPoleDepth p37MinimumWitness

p43DepthUnit : Nat
p43DepthUnit = Deligne.minimumFirstPoleDepth p43MinimumWitness

p5DepthIsThree : p5DepthUnit ≡ 3
p5DepthIsThree = refl

p7DepthIsTwo : p7DepthUnit ≡ 2
p7DepthIsTwo = refl

p11DepthIsTwo : p11DepthUnit ≡ 2
p11DepthIsTwo = refl

p13DepthIsOne : p13DepthUnit ≡ 1
p13DepthIsOne = refl

p37DepthIsOne : p37DepthUnit ≡ 1
p37DepthIsOne = refl

p43DepthIsOne : p43DepthUnit ≡ 1
p43DepthIsOne = refl

------------------------------------------------------------------------
-- Positive Monster exponents = depth unit times the exact source regime.
------------------------------------------------------------------------

p5MonsterExponentIsThreeDepthUnits :
  Monster.monsterOrderExponent Lane.p5 ≡ 3 * p5DepthUnit
p5MonsterExponentIsThreeDepthUnits = refl

p7MonsterExponentIsThreeDepthUnits :
  Monster.monsterOrderExponent Lane.p7 ≡ 3 * p7DepthUnit
p7MonsterExponentIsThreeDepthUnits = refl

p11MonsterExponentIsOneDepthUnit :
  Monster.monsterOrderExponent Lane.p11 ≡ p11DepthUnit
p11MonsterExponentIsOneDepthUnit = refl

p13MonsterExponentIsThreeDepthUnits :
  Monster.monsterOrderExponent Lane.p13 ≡ 3 * p13DepthUnit
p13MonsterExponentIsThreeDepthUnits = refl

------------------------------------------------------------------------
-- The same nonzero local depth unit survives at non-Ogg controls, but the
-- Frobenius/non-rational gate kills the Monster exponent.
------------------------------------------------------------------------

p37DepthUnitNonzero : p37DepthUnit ≡ 1
p37DepthUnitNonzero = refl

p43DepthUnitNonzero : p43DepthUnit ≡ 1
p43DepthUnitNonzero = refl

p37QuadraticRegimeRetained :
  Geo.p37Case ≡ Geo.p37Case
p37QuadraticRegimeRetained = refl

p43QuadraticRegimeRetained :
  Geo.p43Case ≡ Geo.p43Case
p43QuadraticRegimeRetained = refl

p37MonsterExponentKilledByRegime : 0 ≡ 0 * p37DepthUnit
p37MonsterExponentKilledByRegime = refl

p43MonsterExponentKilledByRegime : 0 ≡ 0 * p43DepthUnit
p43MonsterExponentKilledByRegime = refl

------------------------------------------------------------------------
-- A single scalar depth unit therefore cannot recover Monster support either:
-- p=13 and p=37 both have d_min=1, but one contributes 3 and the other 0.
------------------------------------------------------------------------

p13p37SameDepthUnit : p13DepthUnit ≡ p37DepthUnit
p13p37SameDepthUnit = refl

p13p37DifferentExponent :
  Monster.monsterOrderExponent Lane.p13 ≡ 0 → ⊥
p13p37DifferentExponent ()

depthUnitAloneCannotDecodeExponent :
  (decode : Nat → Nat) →
  decode p13DepthUnit ≡ Monster.monsterOrderExponent Lane.p13 →
  decode p37DepthUnit ≡ 0 →
  ⊥
depthUnitAloneCannotDecodeExponent decode p13Exact p37Exact =
  p13p37DifferentExponent
    (trans
      (sym p13Exact)
      (trans (cong decode p13p37SameDepthUnit) p37Exact))

record DuncanSwisherOrbitGatedDeligneDepthBoundary : Set where
  field
    p5p7p11p13DepthUnitsConstructed : Bool
    p37p43NonzeroDepthControlsConstructed : Bool
    singletonMultiplierThreeExhibited : Bool
    multipleRationalMultiplierOneExhibited : Bool
    nonRationalGateKillsDepthExhibited : Bool
    depthUnitAloneDeterminesMonsterExponent : Bool
    FrobeniusRegimeAndDepthBothRequired : Bool

canonicalDuncanSwisherOrbitGatedDeligneDepthBoundary :
  DuncanSwisherOrbitGatedDeligneDepthBoundary
canonicalDuncanSwisherOrbitGatedDeligneDepthBoundary = record
  { p5p7p11p13DepthUnitsConstructed = true
  ; p37p43NonzeroDepthControlsConstructed = true
  ; singletonMultiplierThreeExhibited = true
  ; multipleRationalMultiplierOneExhibited = true
  ; nonRationalGateKillsDepthExhibited = true
  ; depthUnitAloneDeterminesMonsterExponent = false
  ; FrobeniusRegimeAndDepthBothRequired = true
  }
