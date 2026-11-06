{-# OPTIONS --safe #-}
module DASHI.Foundations.BishopSignTwistedFiniteCauchyCoefficientExact where

------------------------------------------------------------------------
-- K05: ALL-N CAUCHY COEFFICIENT SCALING BY THE ORIGINAL (-1)^n.
--
-- For any two Bishop-real coefficient histories a,b and n,
--
--   C_n(((-1)^k a_k),((-1)^k b_k))
--       ~= (-1)^n C_n(a,b).
--
-- This is proved in the actual pinned Bishop setoid semiring by
-- sum-cong on the FIN(suc n) coefficient index. The index bound is
-- the genuine stdlib FinP.toℕ≤pred[n] proof, not a mathematical
-- "for all k" assertion that would be false under Nat truncation.
--
-- No original trig addition, log inverse or complex exp is imported.
-- Sources: Cauchy, Newton; Bishop/Bridges, Murray/Csimma pinned
-- real-power addition, DASHI original finite Cauchy owner.
-- Golden Agda --safe kernel acceptance pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (toℕ)
import Data.Fin.Properties as FinP
import Data.Nat.Base as N
import Data.Nat.Properties as NP
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

import Algebra.Properties.Semiring.Sum as SemiringSum
import Real as R
import RealProperties as RP

import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Term
import DASHI.Foundations.BishopRound11SignedFactorialExponentEncodingExact as Encoding

module BishopSum = SemiringSum RP.+-*-semiring

twist :
  (Nat → R.ℝ) →
  Nat → R.ℝ
twist coefficients k =
  R._*_ (Term.alternatingSign k) (coefficients k)

indexPlusTruncatedComplement :
  (n k : Nat) →
  k N.≤ n →
  k N.+ (n N.∸ k) ≡ n
indexPlusTruncatedComplement n k k≤n =
  trans
    (NP.+-comm k (n N.∸ k))
    (NP.m∸n+n≡m k≤n)

signsMultiplyAtCauchyIndex :
  (n k : Nat) →
  k N.≤ n →
  R._≃_
    (R._*_
      (Term.alternatingSign k)
      (Term.alternatingSign (n N.∸ k)))
    (Term.alternatingSign n)
signsMultiplyAtCauchyIndex n k k≤n =
  RP.≃-trans
    (Encoding.alternatingSignAddition k (n N.∸ k))
    (RP.≃-refl₂
      (cong Term.alternatingSign
        (indexPlusTruncatedComplement n k k≤n)))

signedCauchySummandFactor :
  (left right : Nat → R.ℝ) →
  (n k : Nat) →
  k N.≤ n →
  R._≃_
    (R._*_
      (twist left k)
      (twist right (n N.∸ k)))
    (R._*_
      (Term.alternatingSign n)
      (R._*_ (left k) (right (n N.∸ k))))
signedCauchySummandFactor left right n k k≤n =
  let
    firstSign = Term.alternatingSign k
    secondSign = Term.alternatingSign (n N.∸ k)
    a = left k
    b = right (n N.∸ k)
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (solve 4
      (λ first second left′ right′ →
        (first ⊗ left′) ⊗ (second ⊗ right′)
        ⊜ (first ⊗ second) ⊗ (left′ ⊗ right′))
      RP.≃-refl firstSign secondSign a b)
    (RP.*-congʳ
      (signsMultiplyAtCauchyIndex n k k≤n))

rowCauchyCoefficientRespectsTerms :
  (left right selectedLeft selectedRight : Nat → R.ℝ) →
  (leftEquivalent : ∀ k → R._≃_ (left k) (selectedLeft k)) →
  (rightEquivalent : ∀ k → R._≃_ (right k) (selectedRight k)) →
  (n : Nat) →
  R._≃_
    (Row.cauchyCoefficient left right n)
    (Row.cauchyCoefficient selectedLeft selectedRight n)
rowCauchyCoefficientRespectsTerms
    left right selectedLeft selectedRight leftEq rightEq n =
  BishopSum.sum-cong-≋
    (λ index →
      let k = toℕ index in
      RP.*-cong
        (leftEq k)
        (rightEq (n N.∸ k)))

twistedCauchyCoefficient :
  (left right : Nat → R.ℝ) →
  (n : Nat) →
  R._≃_
    (Row.cauchyCoefficient
      (twist left) (twist right) n)
    (R._*_
      (Term.alternatingSign n)
      (Row.cauchyCoefficient left right n))
twistedCauchyCoefficient left right n =
  RP.≃-trans
    (BishopSum.sum-cong-≋
      (λ index →
        signedCauchySummandFactor
          left right n (toℕ index)
          (FinP.toℕ≤pred[n] index)))
    (RP.≃-symm
      (BishopSum.*-distribˡ-sum
        (Term.alternatingSign n)
        (λ index →
          R._*_
            (left (toℕ index))
            (right (n N.∸ toℕ index)))))
