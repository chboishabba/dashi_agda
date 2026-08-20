module DASHI.Physics.Closure.NSTriadKNFixedShiftConcreteFalsifiersRound62Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND 62 CONCRETE-C CONTRIBUTION
--
-- Make C falsification-first on the literal owner/block quantities.
--
-- The universal upstream claims eventually required are
--
--   X_n <= K T_n,
--   A_HHg,n <= a_HHg T_n,
--   A_Com,n <= a_Com T_n,
--
-- where T_n = C r^n is the EXISTING fixed-block target.  Before trying to
-- prove these universally, one bad block should kill a proposed constant
-- immediately.  This file packages exactly those local counterexamples and
-- proves that each refutes the corresponding universal scale law.
--
-- Crucially this module imports no sharp-capacity or Young-allocation theorem.
-- It depends only on the owner quantities and the pre-existing block target,
-- so it cannot manufacture K or a by feeding B_* back into C.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Nullary using (¬_)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine
import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block

blockTarget : Block.RationalFixedBlockDecay → Nat → ℚ
blockTarget block n =
  Block.scaledTarget (Block.constant block) (Block.r block) n

criticalValue :
  (balances : Nat → Nine.NineOwnerCriticalBalance) → Nat → ℚ
criticalValue balances n =
  Owner.integralCritical (Nine.environment (balances n))

hhGoodDataValue :
  (balances : Nat → Nine.NineOwnerCriticalBalance) → Nat → ℚ
hhGoodDataValue balances n =
  Owner.dataRemainder (Owner.hhGood (Nine.family (balances n)))

comDataValue :
  (balances : Nat → Nine.NineOwnerCriticalBalance) → Nat → ℚ
comDataValue balances n =
  Owner.dataRemainder (Owner.com (Nine.family (balances n)))

twoSoftDataValue :
  (balances : Nat → Nine.NineOwnerCriticalBalance) → Nat → ℚ
twoSoftDataValue balances n =
  hhGoodDataValue balances n + comDataValue balances n

------------------------------------------------------------------------
-- One-block critical-scale falsifier.
------------------------------------------------------------------------

record CriticalScaleCounterexample
    (balances : Nat → Nine.NineOwnerCriticalBalance)
    (block : Block.RationalFixedBlockDecay)
    (candidateK : ℚ) : Set where
  field
    blockIndex : Nat
    candidateTargetStrictlyBelowCritical :
      candidateK * blockTarget block blockIndex
      < criticalValue balances blockIndex

open CriticalScaleCounterexample public

criticalCounterexampleRefutesUniformScale :
  ∀ {balances block candidateK} →
  CriticalScaleCounterexample balances block candidateK →
  ((n : Nat) →
    criticalValue balances n ≤ candidateK * blockTarget block n) →
  ⊥
criticalCounterexampleRefutesUniformScale failure uniform =
  ℚP.<-irrefl refl
    (ℚP.<-≤-trans
      (candidateTargetStrictlyBelowCritical failure)
      (uniform (blockIndex failure)))

------------------------------------------------------------------------
-- One-block HH-good smooth-data candidate falsifier.
------------------------------------------------------------------------

record HHGoodDataScaleCounterexample
    (balances : Nat → Nine.NineOwnerCriticalBalance)
    (block : Block.RationalFixedBlockDecay)
    (candidateA : ℚ) : Set where
  field
    blockIndex : Nat
    candidateTargetStrictlyBelowHHGood :
      candidateA * blockTarget block blockIndex
      < hhGoodDataValue balances blockIndex

open HHGoodDataScaleCounterexample public

hhGoodCounterexampleRefutesUniformScale :
  ∀ {balances block candidateA} →
  HHGoodDataScaleCounterexample balances block candidateA →
  ((n : Nat) →
    hhGoodDataValue balances n ≤ candidateA * blockTarget block n) →
  ⊥
hhGoodCounterexampleRefutesUniformScale failure uniform =
  ℚP.<-irrefl refl
    (ℚP.<-≤-trans
      (candidateTargetStrictlyBelowHHGood failure)
      (uniform (blockIndex failure)))

------------------------------------------------------------------------
-- One-block Com-data candidate falsifier.
------------------------------------------------------------------------

record ComDataScaleCounterexample
    (balances : Nat → Nine.NineOwnerCriticalBalance)
    (block : Block.RationalFixedBlockDecay)
    (candidateA : ℚ) : Set where
  field
    blockIndex : Nat
    candidateTargetStrictlyBelowCom :
      candidateA * blockTarget block blockIndex
      < comDataValue balances blockIndex

open ComDataScaleCounterexample public

comCounterexampleRefutesUniformScale :
  ∀ {balances block candidateA} →
  ComDataScaleCounterexample balances block candidateA →
  ((n : Nat) →
    comDataValue balances n ≤ candidateA * blockTarget block n) →
  ⊥
comCounterexampleRefutesUniformScale failure uniform =
  ℚP.<-irrefl refl
    (ℚP.<-≤-trans
      (candidateTargetStrictlyBelowCom failure)
      (uniform (blockIndex failure)))

------------------------------------------------------------------------
-- Combined two-soft local test.  This is stronger as a falsifier than checking
-- the two components separately when only their sum matters downstream.
------------------------------------------------------------------------

record TwoSoftDataScaleCounterexample
    (balances : Nat → Nine.NineOwnerCriticalBalance)
    (block : Block.RationalFixedBlockDecay)
    (candidateA : ℚ) : Set where
  field
    blockIndex : Nat
    candidateTargetStrictlyBelowTwoSoft :
      candidateA * blockTarget block blockIndex
      < twoSoftDataValue balances blockIndex

open TwoSoftDataScaleCounterexample public

twoSoftCounterexampleRefutesUniformScale :
  ∀ {balances block candidateA} →
  TwoSoftDataScaleCounterexample balances block candidateA →
  ((n : Nat) →
    twoSoftDataValue balances n ≤ candidateA * blockTarget block n) →
  ⊥
twoSoftCounterexampleRefutesUniformScale failure uniform =
  ℚP.<-irrefl refl
    (ℚP.<-≤-trans
      (candidateTargetStrictlyBelowTwoSoft failure)
      (uniform (blockIndex failure)))

------------------------------------------------------------------------
-- The strict-gap numerical falsifier itself.  Once candidate coefficients are
-- extracted upstream, a >= r-q kills the sharp positive-capacity branch.
------------------------------------------------------------------------

record TwoSoftStrictGapFailure
    (block : Block.RationalFixedBlockDecay)
    (hhGoodScale comScale : ℚ) : Set where
  field
    gapNotStrict :
      Block.r block - Block.q block ≤ hhGoodScale + comScale

open TwoSoftStrictGapFailure public

twoSoftGapFailureRefutesStrictGap :
  ∀ {block hhGoodScale comScale} →
  TwoSoftStrictGapFailure block hhGoodScale comScale →
  ¬ ((hhGoodScale + comScale) < (Block.r block - Block.q block))
twoSoftGapFailureRefutesStrictGap failure strict =
  ℚP.<-irrefl refl
    (ℚP.<-≤-trans strict (gapNotStrict failure))

concreteCriticalScaleFalsifierClosed : Bool
concreteCriticalScaleFalsifierClosed = true

concreteTwoSoftDataFalsifierClosed : Bool
concreteTwoSoftDataFalsifierClosed = true

concreteStrictGapFalsifierClosed : Bool
concreteStrictGapFalsifierClosed = true

concreteCriticalScaleFalsifierClosedIsTrue :
  concreteCriticalScaleFalsifierClosed ≡ true
concreteCriticalScaleFalsifierClosedIsTrue = refl

concreteTwoSoftDataFalsifierClosedIsTrue :
  concreteTwoSoftDataFalsifierClosed ≡ true
concreteTwoSoftDataFalsifierClosedIsTrue = refl

concreteStrictGapFalsifierClosedIsTrue :
  concreteStrictGapFalsifierClosed ≡ true
concreteStrictGapFalsifierClosedIsTrue = refl
