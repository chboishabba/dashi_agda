module DASHI.Physics.Closure.NSRound180SignedSchurWeldExact where

open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; _+_; _-_; _≤_)
import Data.Rational.Properties as Q
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)
import DASHI.Analysis.BlockSchurCoercivity as Schur
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3

Cell : Set
Cell = C3.Complex3 R180.F

totalMass : List Cell → ℚ
totalMass cells = L2.complex3NormSquared (R180.sumCells cells)

-- Both upper and lower signed debt budgets use the actual R180 ledger.
lowerGram : ∀ cells diagonal debt →
  diagonal ≤ R180.cellMassSum cells →
  debt ≤ R180.gramDebt cells →
  diagonal + debt ≤ totalMass cells
lowerGram cells diagonal debt hd hg =
  subst (diagonal + debt ≤_) (sym (R180.finiteFibreGramLedger cells))
    (Q.+-mono-≤ hd hg)

upperGram : ∀ cells diagonal debt →
  R180.cellMassSum cells ≤ diagonal →
  R180.gramDebt cells ≤ debt →
  totalMass cells ≤ diagonal + debt
upperGram cells diagonal debt hd hg =
  subst (_≤ diagonal + debt) (sym (R180.finiteFibreGramLedger cells))
    (Q.+-mono-≤ hd hg)

-- Existing Schur order owner, instantiated on exact rationals.
rationalSchur : Schur.SchurOrderLaws ℚ
rationalSchur = record
  { _≤_ = _≤_
  ; _⊖_ = _-_
  ; subtractLowerBound = λ hd hc _ → Q.+-mono-≤ hd (Q.neg-mono-≤ hc)
  }

-- The original R180 mass is the cross-correction, not a surrogate.
-- Unit/weighted test normalization is external to this exact finite lemma.
physicalSchur :
  ∀ (cells : List Cell) (d δ diagonal debt : ℚ) →
  δ ≤ d →
  R180.cellMassSum cells ≤ diagonal →
  R180.gramDebt cells ≤ debt →
  diagonal + debt ≤ δ →
  δ - (diagonal + debt) ≤ d - totalMass cells
physicalSchur cells d δ diagonal debt hd hm hg hb =
  Schur.subtractLowerBound rationalSchur hd
    (upperGram cells diagonal debt hm hg) hb
