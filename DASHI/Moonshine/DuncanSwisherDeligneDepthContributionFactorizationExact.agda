module DASHI.Moonshine.DuncanSwisherDeligneDepthContributionFactorizationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
--
-- Source inputs already isolated elsewhere in the repository:
--
--   Theorem 1.2 : exact supersingular exponent-depth cases;
--   equation 1.8: 2 v_p(J_1-J_{p+}) = m_p on the zero-quadratic branch;
--   Theorem 1.1 : the three modular-function contributions sum to v_p(|M|);
--   Proposition 3.1: the minimum Deligne first-pole depth d_min satisfies
--                    2 d_min = m_p.
--
-- DASHI CONTRIBUTION
--
-- Compose those same-source surfaces into the cleaner mechanism
--
--   Fricke contribution = d_min,
--
-- with residual depth
--
--   0       on the multiple-rational branch,
--   2 d_min on the singleton-rational branch.
--
-- Thus the entire positive Monster exponent is measured in units of the
-- minimum Deligne first-pole depth:
--
--   valuation = d_min   or   3 d_min.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_; _+_; _*_)
import Data.Nat.Properties as NatP

import DASHI.Moonshine.DuncanSwisherMonsterExponentFormulaExact as DS
import DASHI.Moonshine.DuncanSwisherModularValuationDepthMechanismExact as Modular

------------------------------------------------------------------------
-- Generic bridge between the source's minimum automorphism order and an actual
-- minimum first-pole depth witness.
------------------------------------------------------------------------

record DeligneMinimumDepthWitness
    {p : Nat} {prime : Data.Nat.Primality.Prime p} {ge5 : 5 ≤ p}
    (E : DS.DuncanSwisherExponentAuthority p prime ge5) : Set where
  constructor deligne-minimum-depth-witness
  field
    minimumFirstPoleDepth : Nat
    doubledDepthIsMinimumAut :
      2 * minimumFirstPoleDepth ≡ DS.minimumAutomorphismOrder E

open DeligneMinimumDepthWitness public

cancelDouble : {a b : Nat} → 2 * a ≡ 2 * b → a ≡ b
cancelDouble {a} {b} equality = NatP.*-cancelˡ-≡ a b 2 equality

------------------------------------------------------------------------
-- On the zero-pair branch equation (1.8) identifies the Fricke contribution
-- exactly with the minimum Deligne first-pole depth.
------------------------------------------------------------------------

frickeContributionEqualsMinimumDepth :
  {p : Nat} {prime : Data.Nat.Primality.Prime p} {ge5 : 5 ≤ p} →
  (E : DS.DuncanSwisherExponentAuthority p prime ge5) →
  (M : Modular.DuncanSwisherModularValuationAuthority p prime ge5 E) →
  (D : DeligneMinimumDepthWitness E) →
  DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeCombinatoricsExact.pairedCount
    (DS.sharedGeometry p prime ge5) ≡ 0 →
  Modular.frickeContribution M ≡ minimumFirstPoleDepth D
frickeContributionEqualsMinimumDepth E M D pairZero =
  cancelDouble
    (trans
      (Modular.frickeContributionAtZeroPairDefect M pairZero)
      (sym (doubledDepthIsMinimumAut D)))

------------------------------------------------------------------------
-- Constructor-indexed Deligne-depth residual classification.
------------------------------------------------------------------------

data DeligneDepthContributionPattern
    (fricke residual depth : Nat) : Set where

  multipleRationalPattern :
    fricke ≡ depth →
    residual ≡ 0 →
    DeligneDepthContributionPattern fricke residual depth

  singletonRationalPattern :
    fricke ≡ depth →
    residual ≡ 2 * depth →
    DeligneDepthContributionPattern fricke residual depth

  quadraticPattern :
    fricke ≡ 0 →
    residual ≡ 0 →
    DeligneDepthContributionPattern fricke residual depth

------------------------------------------------------------------------
-- Derive the pattern from the canonical Theorem-1.2 branch and the already
-- derived modular-residual theorem.
------------------------------------------------------------------------

deligneDepthContributionPattern :
  {p : Nat} {prime : Data.Nat.Primality.Prime p} {ge5 : 5 ≤ p} →
  (E : DS.DuncanSwisherExponentAuthority p prime ge5) →
  (M : Modular.DuncanSwisherModularValuationAuthority p prime ge5 E) →
  (D : DeligneMinimumDepthWitness E) →
  (case : DS.DuncanSwisherExponentCase
    (DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeCombinatoricsExact.fixedCount
      (DS.sharedGeometry p prime ge5))
    (DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeCombinatoricsExact.pairedCount
      (DS.sharedGeometry p prime ge5))
    (DS.monsterValuation E)
    (DS.minimumAutomorphismOrder E)) →
  DeligneDepthContributionPattern
    (Modular.frickeContribution M)
    (Modular.primeLevelContribution M + Modular.squareLevelContribution M)
    (minimumFirstPoleDepth D)
deligneDepthContributionPattern E M D
  case@(DS.multipleRational fixedMany pairZero doubled) =
  multipleRationalPattern
    (frickeContributionEqualsMinimumDepth E M D pairZero)
    (Modular.modularResidualClassification E M case)
deligneDepthContributionPattern E M D
  case@(DS.singletonRational fixedOne pairZero doubled) =
  let
    frickeExact = frickeContributionEqualsMinimumDepth E M D pairZero
    residualIsMinimumAut = Modular.modularResidualClassification E M case
    residualIsDoubleDepth :
      Modular.primeLevelContribution M + Modular.squareLevelContribution M
      ≡ 2 * minimumFirstPoleDepth D
    residualIsDoubleDepth =
      trans residualIsMinimumAut (sym (doubledDepthIsMinimumAut D))
  in
  singletonRationalPattern frickeExact residualIsDoubleDepth
deligneDepthContributionPattern E M D
  case@(DS.quadraticPresent pairPositive valuationZero minTwo) =
  let
    allZero = Modular.modularResidualClassification E M case
  in
  quadraticPattern (proj₁ allZero) (trans (proj₁ (proj₂ allZero)) (sym (NatP.+-identityʳ 0)))

------------------------------------------------------------------------
-- p=11 exact depth witness: m_11=4, so d_min=2.
------------------------------------------------------------------------

import DASHI.Moonshine.DuncanSwisherDeligneAutomorphismDepthBridgeExact as AutDepth
import DASHI.Moonshine.DuncanSwisherMonsterExponentGeometryExact as Geo
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Monster

-- Concrete arithmetic shadow of the generic bridge.
p11DepthUnit : Nat
p11DepthUnit = AutDepth.minimumFirstPoleDepth AutDepth.p11MinimumWitness

p11DepthUnitIsTwo : p11DepthUnit ≡ 2
p11DepthUnitIsTwo = refl

p11MonsterExponentIsOneDepthUnit :
  Monster.monsterOrderExponent Lane.p11 ≡ p11DepthUnit
p11MonsterExponentIsOneDepthUnit = refl

record DuncanSwisherDeligneDepthContributionBoundary : Set where
  field
    minimumAutReexpressedAsDoubleDeligneDepth : Bool
    frickeContributionEqualsMinimumDepthDerived : Bool
    multipleRationalResidualZeroRetained : Bool
    singletonResidualEqualsTwoDepthUnitsDerived : Bool
    quadraticBranchAllContributionsZeroRetained : Bool
    p11ExponentEqualsOneDepthUnit : Bool
    DelignePartialFractionExpansionReprovedHere : Bool

canonicalDuncanSwisherDeligneDepthContributionBoundary :
  DuncanSwisherDeligneDepthContributionBoundary
canonicalDuncanSwisherDeligneDepthContributionBoundary = record
  { minimumAutReexpressedAsDoubleDeligneDepth = true
  ; frickeContributionEqualsMinimumDepthDerived = true
  ; multipleRationalResidualZeroRetained = true
  ; singletonResidualEqualsTwoDepthUnitsDerived = true
  ; quadraticBranchAllContributionsZeroRetained = true
  ; p11ExponentEqualsOneDepthUnit = true
  ; DelignePartialFractionExpansionReprovedHere = false
  }
