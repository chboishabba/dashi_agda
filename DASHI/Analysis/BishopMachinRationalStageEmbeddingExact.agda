module DASHI.Analysis.BishopMachinRationalStageEmbeddingExact where

------------------------------------------------------------------------
-- K04a: EXACT RATIONAL MACHIN STAGES -> ORIGINAL BISHOP SERIES.
--
-- John Machin, 1706: pi/4 = 4 atan(1/5) - atan(1/239).
-- Bishop & Bridges, Constructive Analysis (1985),
-- DOI 10.1007/978-3-642-61667-9;
-- Murray, Constructive Analysis in Agda (2022), arXiv:2205.08354.
-- Code source: pinned viktorcsimma/bishop RealProperties and Sequence.
--
-- The finite q_n uses the original unnormalised rational arithmetic
-- rather than an unrelated real and the original Machin signed atan terms.
-- The theorem is setoid equality, NOT propositional equality of reals.
-- Computational tests and compiler/kernel receipts remain separate.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised as Q using
  (ℚᵘ; 0ℚᵘ; 1ℚᵘ; _+_; _*_; _-_; -_)
import Real as Bishop
import RealProperties as RP
import Sequence as Series

import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Terms
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Estimates
import DASHI.Analysis.BishopMachinSignedFiniteHistoryExact as Signed

-- Signed powers and odd rational coefficients agree with the actual
-- source's alternation and 2n+1 index, including stage zero.
qPow : ℚᵘ → Nat → ℚᵘ
qPow x zero = 1ℚᵘ
qPow x (suc k) = qPow x k Q.* x

qMinusOne : ℚᵘ
qMinusOne = Q.- 1ℚᵘ

qSign : Nat → ℚᵘ
qSign = qPow qMinusOne

qAtanTerm : ℚᵘ → Nat → ℚᵘ
qAtanTerm x k =
  qSign k Q.*
    (Machin.inverseOddRational k
      Q.* qPow x (Estimates.oddExponent k))

-- Its declared coefficients are the literal 16/4 from the
-- original Bishop Machin construction.
qMachinTerm : Nat → ℚᵘ
qMachinTerm k =
  (Machin.sixteen Q.* qAtanTerm Machin.oneFifth k)
    Q.- (Machin.four Q.*
      qAtanTerm Machin.oneTwoHundredThirtyNinth k)

-- q_n = sum_{j<n} of the exact rational terms. In particular q_0=0;
-- the executable script begins at n=1 only for its stated error bound.
qMachinStage : Nat → ℚᵘ
qMachinStage zero = 0ℚᵘ
qMachinStage (suc n) = qMachinStage n Q.+ qMachinTerm n

qPowEmbeds : (x : ℚᵘ) (k : Nat) →
  Bishop._≃_
    (Bishop._⋆ (qPow x k))
    (Bishop.pow (Bishop._⋆ x) k)
qPowEmbeds x zero = RP.≃-refl
qPowEmbeds x (suc k) =
  RP.≃-trans
    (RP.⋆-distrib-* (qPow x k) x)
    (RP.*-cong (qPowEmbeds x k) RP.≃-refl)

qMinusOneEmbeds :
  Bishop._≃_
    (Bishop._⋆ qMinusOne)
    Terms.bishopMinusOne
qMinusOneEmbeds = RP.⋆-distrib-neg 1ℚᵘ

qSignEmbeds : (k : Nat) →
  Bishop._≃_
    (Bishop._⋆ (qSign k))
    (Terms.alternatingSign k)
qSignEmbeds k =
  RP.≃-trans
    (qPowEmbeds qMinusOne k)
    (RP.pow-cong k qMinusOneEmbeds)

qAtanTermEmbeds : (x : ℚᵘ) (k : Nat) →
  Bishop._≃_
    (Bishop._⋆ (qAtanTerm x k))
    (Machin.atanSignedTerm (Bishop._⋆ x) k)
qAtanTermEmbeds x k =
  RP.≃-trans
    (RP.⋆-distrib-* (qSign k)
      (Machin.inverseOddRational k
        Q.* qPow x (Estimates.oddExponent k)))
    (RP.*-cong
      (qSignEmbeds k)
      (RP.≃-trans
        (RP.⋆-distrib-*
          (Machin.inverseOddRational k)
          (qPow x (Estimates.oddExponent k)))
        (RP.*-cong
          RP.≃-refl
          (qPowEmbeds x (Estimates.oddExponent k)))))

qMachinTermEmbeds : (k : Nat) →
  Bishop._≃_
    (Bishop._⋆ (qMachinTerm k))
    (Signed.machinSignedTerm k)
qMachinTermEmbeds k =
  RP.≃-trans
    (RP.⋆-distrib-to-p⋆-q⋆
      (Machin.sixteen Q.* qAtanTerm Machin.oneFifth k)
      (Machin.four Q.*
        qAtanTerm Machin.oneTwoHundredThirtyNinth k))
    (RP.≃-trans
      (RP.+-cong
        (RP.≃-trans
          (RP.⋆-distrib-* Machin.sixteen
            (qAtanTerm Machin.oneFifth k))
          (RP.*-cong RP.≃-refl
            (qAtanTermEmbeds Machin.oneFifth k)))
        (RP.-‿cong
          (RP.≃-trans
            (RP.⋆-distrib-* Machin.four
              (qAtanTerm Machin.oneTwoHundredThirtyNinth k))
            (RP.*-cong RP.≃-refl
              (qAtanTermEmbeds Machin.oneTwoHundredThirtyNinth k)))))
      RP.≃-refl)

-- All-input finite history identity: rational q_n maps to the same
-- Sequence.SeriesOf terms on the canonical Bishop real carrier.
qMachinStageEmbedsAsOriginalBishopPartial : (n : Nat) →
  Bishop._≃_
    (Bishop._⋆ (qMachinStage n))
    (Signed.machinSignedPartialStage n)
qMachinStageEmbedsAsOriginalBishopPartial zero =
  RP.≃-refl
qMachinStageEmbedsAsOriginalBishopPartial (suc n) =
  RP.≃-trans
    (RP.⋆-distrib-+ (qMachinStage n) (qMachinTerm n))
    (RP.+-cong
      (qMachinStageEmbedsAsOriginalBishopPartial n)
      (qMachinTermEmbeds n))

------------------------------------------------------------------------
-- K04b same-object convergence: this is a theorem on the actual
-- Bishop-real embedding of EVERY rational q_n, not on an abstract
-- Real or a merely supplied AnalyticLimitAttachment. The quantitative
-- e_n / 4*25^(-n) modulus is separate and remains to be kernel proved.
------------------------------------------------------------------------

rationalMachinStagesConvergeToOriginalMachinPi :
  Series._ConvergesTo_
    (λ n → Bishop._⋆ (qMachinStage n))
    Machin.bishopMachinPi
rationalMachinStagesConvergeToOriginalMachinPi =
  Series.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc n) →
      RP.≃-symm
        (qMachinStageEmbedsAsOriginalBishopPartial (suc n))})
    ( Machin.bishopMachinPi
    , Signed.machinSignedPartialConvergesToOriginalMachinPi )
