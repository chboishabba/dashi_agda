module DASHI.Moonshine.JInvariant369PrincipalLevelTowerExact where

------------------------------------------------------------------------
-- PRINCIPAL CONGRUENCE LEVEL TOWER AT 3, 9, 27
--
-- This module pays the group-level part of the 3 -> 9 -> 27 question without
-- pretending to construct the full analytic modular curves X(N).
--
-- For g = [a b; c d] in SL2(Z), membership in Gamma(N) is represented by
--
--   a = 1 + N qa
--   b =     N qb
--   c =     N qc
--   d = 1 + N qd.
--
-- We prove
--
--   Gamma(27) subset Gamma(9) subset Gamma(3)
--
-- and show T^N belongs to Gamma(N) for N = 3,9,27.  Combined with the cusp
-- fibre owner, this gives the canonical covering direction underlying
--
--   Z/27 -> Z/9 -> Z/3
--
-- while keeping the full deck group and analytic X(N) construction separate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl; trans; cong)
open import Data.Integer using (ℤ; 0ℤ; 1ℤ; +_; _+_; _*_)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver

import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Modular
import DASHI.Moonshine.JInvariant369ModularLevelCuspObserversExact as Cusp

level3Z level9Z level27Z : ℤ
level3Z = + 3
level9Z = + 9
level27Z = + 27

record InPrincipalLevel
    (level : ℤ)
    (g : Modular.SL2Z) : Set where
  constructor in-principal-level
  field
    qa qb qc qd : ℤ

    aCongruence :
      Modular.a g ≡ 1ℤ + level * qa

    bCongruence :
      Modular.b g ≡ level * qb

    cCongruence :
      Modular.c g ≡ level * qc

    dCongruence :
      Modular.d g ≡ 1ℤ + level * qd

open InPrincipalLevel public

------------------------------------------------------------------------
-- 1. T^N is in Gamma(N).
------------------------------------------------------------------------

translationPowerAtLevel :
  (n : Nat) →
  Modular.SL2Z
translationPowerAtLevel =
  Cusp.translationPower

translationPowerMembership :
  (n : Nat) →
  InPrincipalLevel (+ n) (translationPowerAtLevel n)
translationPowerMembership n =
  in-principal-level
    0ℤ 1ℤ 0ℤ 0ℤ
    refl refl refl refl

T3InGamma3 :
  InPrincipalLevel level3Z (translationPowerAtLevel 3)
T3InGamma3 = translationPowerMembership 3

T9InGamma9 :
  InPrincipalLevel level9Z (translationPowerAtLevel 9)
T9InGamma9 = translationPowerMembership 9

T27InGamma27 :
  InPrincipalLevel level27Z (translationPowerAtLevel 27)
T27InGamma27 = translationPowerMembership 27

------------------------------------------------------------------------
-- 2. Exact principal-subgroup inclusions.
------------------------------------------------------------------------

gamma9ToGamma3 :
  ∀ {g} →
  InPrincipalLevel level9Z g →
  InPrincipalLevel level3Z g
gamma9ToGamma3 {g} h =
  in-principal-level
    (3 * qa h)
    (3 * qb h)
    (3 * qc h)
    (3 * qd h)
    aProof bProof cProof dProof
  where
  aScale :
    1ℤ + level9Z * qa h
    ≡
    1ℤ + level3Z * (3 * qa h)
  aScale =
    solve 1
      (λ q →
        (con 1 :+ con 9 :* q)
        := (con 1 :+ con 3 :* (con 3 :* q)))
      refl
      (qa h)

  bScale :
    level9Z * qb h
    ≡
    level3Z * (3 * qb h)
  bScale =
    solve 1
      (λ q →
        (con 9 :* q)
        := (con 3 :* (con 3 :* q)))
      refl
      (qb h)

  cScale :
    level9Z * qc h
    ≡
    level3Z * (3 * qc h)
  cScale =
    solve 1
      (λ q →
        (con 9 :* q)
        := (con 3 :* (con 3 :* q)))
      refl
      (qc h)

  dScale :
    1ℤ + level9Z * qd h
    ≡
    1ℤ + level3Z * (3 * qd h)
  dScale =
    solve 1
      (λ q →
        (con 1 :+ con 9 :* q)
        := (con 1 :+ con 3 :* (con 3 :* q)))
      refl
      (qd h)

  aProof = trans (aCongruence h) aScale
  bProof = trans (bCongruence h) bScale
  cProof = trans (cCongruence h) cScale
  dProof = trans (dCongruence h) dScale

gamma27ToGamma9 :
  ∀ {g} →
  InPrincipalLevel level27Z g →
  InPrincipalLevel level9Z g
gamma27ToGamma9 {g} h =
  in-principal-level
    (3 * qa h)
    (3 * qb h)
    (3 * qc h)
    (3 * qd h)
    aProof bProof cProof dProof
  where
  aScale :
    1ℤ + level27Z * qa h
    ≡
    1ℤ + level9Z * (3 * qa h)
  aScale =
    solve 1
      (λ q →
        (con 1 :+ con 27 :* q)
        := (con 1 :+ con 9 :* (con 3 :* q)))
      refl
      (qa h)

  bScale :
    level27Z * qb h
    ≡
    level9Z * (3 * qb h)
  bScale =
    solve 1
      (λ q →
        (con 27 :* q)
        := (con 9 :* (con 3 :* q)))
      refl
      (qb h)

  cScale :
    level27Z * qc h
    ≡
    level9Z * (3 * qc h)
  cScale =
    solve 1
      (λ q →
        (con 27 :* q)
        := (con 9 :* (con 3 :* q)))
      refl
      (qc h)

  dScale :
    1ℤ + level27Z * qd h
    ≡
    1ℤ + level9Z * (3 * qd h)
  dScale =
    solve 1
      (λ q →
        (con 1 :+ con 27 :* q)
        := (con 1 :+ con 9 :* (con 3 :* q)))
      refl
      (qd h)

  aProof = trans (aCongruence h) aScale
  bProof = trans (bCongruence h) bScale
  cProof = trans (cCongruence h) cScale
  dProof = trans (dCongruence h) dScale

gamma27ToGamma3 :
  ∀ {g} →
  InPrincipalLevel level27Z g →
  InPrincipalLevel level3Z g
gamma27ToGamma3 =
  gamma9ToGamma3 ∘ gamma27ToGamma9

------------------------------------------------------------------------
-- 3. The group-level inclusions agree with the cusp covering direction.
--
-- The analytic quotient spaces X(N) are not constructed here; only the
-- principal subgroup inclusion direction and the already-owned cusp fibres are
-- welded.
------------------------------------------------------------------------

record PrincipalLevelCuspTowerReceipt : Set where
  constructor principal-level-cusp-tower-receipt
  field
    gamma27SubsetGamma9 : Bool
    gamma9SubsetGamma3 : Bool
    gamma27SubsetGamma3 : Bool

    t3InGamma3 : Bool
    t9InGamma9 : Bool
    t27InGamma27 : Bool

    cusp27To9ProjectionOwned : Bool
    cusp9To3ProjectionOwned : Bool
    cuspCoveringTranslationEquivariant : Bool

    fullAnalyticX27ToX9ToX3Constructed : Bool
    fullDeckGroupsClaimedCyclic : Bool

canonicalPrincipalLevelCuspTowerReceipt :
  PrincipalLevelCuspTowerReceipt
canonicalPrincipalLevelCuspTowerReceipt =
  principal-level-cusp-tower-receipt
    true true true
    true true true
    true true true
    false false
