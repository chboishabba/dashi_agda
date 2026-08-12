module DASHI.Physics.YangMills.BalabanNormalizedFourAxisMartingaleExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- P. K. Mitter,
-- "The Exact Renormalization Group", arXiv:math-ph/0505008.
-- No DOI recorded for the cited encyclopedia preprint.
--
-- DASHI CONTRIBUTION
--
-- Arbitrary-side four-coordinate martingale decomposition on the literal L^4
-- physical block.  The proof avoids a side-four-only six-cross-term expansion:
-- it iterates the exact one-axis Pythagoras theorem four times.  Consequently
-- no new orthogonality postulate is needed.  For a globally mean-zero field,
-- the terminal four-axis conditional expectation vanishes and the global L2
-- norm is exactly the sum of the four martingale norms.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
import DASHI.Physics.YangMills.BalabanNormalizedAxisAverageExact as Average
import DASHI.Physics.YangMills.BalabanNormalizedAxisAverageNormContractionExact as Norm

average0 :
  ∀ {L} → Average.NormalizedAxisAverageData L → SiteField L → SiteField L
average0 dataSet field = Average.axisAverage dataSet field zeroᵢ

average01 :
  ∀ {L} → Average.NormalizedAxisAverageData L → SiteField L → SiteField L
average01 dataSet field =
  Average.axisAverage dataSet (average0 dataSet field) (sucᵢ zeroᵢ)

average012 :
  ∀ {L} → Average.NormalizedAxisAverageData L → SiteField L → SiteField L
average012 dataSet field =
  Average.axisAverage dataSet (average01 dataSet field)
    (sucᵢ (sucᵢ zeroᵢ))

average0123 :
  ∀ {L} → Average.NormalizedAxisAverageData L → SiteField L → SiteField L
average0123 dataSet field =
  Average.axisAverage dataSet (average012 dataSet field)
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))

martingale0 martingale1 martingale2 martingale3 :
  ∀ {L} → Average.NormalizedAxisAverageData L → SiteField L → SiteField L
martingale0 dataSet field =
  Norm.axisResidual dataSet field zeroᵢ
martingale1 dataSet field =
  Norm.axisResidual dataSet (average0 dataSet field) (sucᵢ zeroᵢ)
martingale2 dataSet field =
  Norm.axisResidual dataSet (average01 dataSet field)
    (sucᵢ (sucᵢ zeroᵢ))
martingale3 dataSet field =
  Norm.axisResidual dataSet (average012 dataSet field)
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))

GlobalMeanZero :
  ∀ {L} → Average.NormalizedAxisAverageData L → SiteField L → Set
GlobalMeanZero dataSet field = ∀ site → average0123 dataSet field site ≡ 0ℚ

terminalNormZero :
  ∀ {L} (dataSet : Average.NormalizedAxisAverageData L)
    (field : SiteField L) → GlobalMeanZero dataSet field →
  Norm.globalNormSq (average0123 dataSet field) ≡ 0ℚ
terminalNormZero {L} dataSet field meanZero =
  trans
    (DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact.sumRationalCong
      (DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier.physicalBlockSites L)
      (λ site → average0123 dataSet field site * average0123 dataSet field site)
      (λ _ → 0ℚ)
      (λ site →
        trans
          (cong (λ value → value * average0123 dataSet field site)
            (meanZero site))
          (cong (0ℚ +_) refl)))
    (zeroSum (DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier.physicalBlockSites L))
  where
  zeroSum : ∀ {A : Set} (values : Agda.Builtin.List.List A) →
    DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact.sumRational values
      (λ _ → 0ℚ) ≡ 0ℚ
  zeroSum Agda.Builtin.List.[] = refl
  zeroSum (Agda.Builtin.List._∷_ value values)
    rewrite zeroSum values = refl

fourAxisVarianceWithTerminal :
  ∀ {L} (dataSet : Average.NormalizedAxisAverageData L)
    (field : SiteField L) →
  Norm.globalNormSq field
  ≡ Norm.globalNormSq (martingale0 dataSet field)
    + (Norm.globalNormSq (martingale1 dataSet field)
    + (Norm.globalNormSq (martingale2 dataSet field)
    + (Norm.globalNormSq (martingale3 dataSet field)
    + Norm.globalNormSq (average0123 dataSet field))))
fourAxisVarianceWithTerminal dataSet field =
  let
    p0 = Norm.axisAveragePythagoras dataSet field zeroᵢ
    p1 = Norm.axisAveragePythagoras dataSet (average0 dataSet field)
      (sucᵢ zeroᵢ)
    p2 = Norm.axisAveragePythagoras dataSet (average01 dataSet field)
      (sucᵢ (sucᵢ zeroᵢ))
    p3 = Norm.axisAveragePythagoras dataSet (average012 dataSet field)
      (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  in
  trans p0
    (trans
      (cong (Norm.globalNormSq (martingale0 dataSet field) +_) p1)
      (trans
        (cong
          (λ value → Norm.globalNormSq (martingale0 dataSet field) + value)
          (cong (Norm.globalNormSq (martingale1 dataSet field) +_) p2))
        (trans
          (cong
            (λ value →
              Norm.globalNormSq (martingale0 dataSet field)
              + (Norm.globalNormSq (martingale1 dataSet field) + value))
            (cong (Norm.globalNormSq (martingale2 dataSet field) +_) p3))
          (ℚRing.solve-∀
            (Norm.globalNormSq (martingale0 dataSet field))
            (Norm.globalNormSq (martingale1 dataSet field))
            (Norm.globalNormSq (martingale2 dataSet field))
            (Norm.globalNormSq (martingale3 dataSet field))
            (Norm.globalNormSq (average0123 dataSet field))))))

fourAxisVarianceDecomposition :
  ∀ {L} (dataSet : Average.NormalizedAxisAverageData L)
    (field : SiteField L) → GlobalMeanZero dataSet field →
  Norm.globalNormSq field
  ≡ Norm.globalNormSq (martingale0 dataSet field)
    + (Norm.globalNormSq (martingale1 dataSet field)
    + (Norm.globalNormSq (martingale2 dataSet field)
    + Norm.globalNormSq (martingale3 dataSet field)))
fourAxisVarianceDecomposition dataSet field meanZero =
  trans
    (fourAxisVarianceWithTerminal dataSet field)
    (trans
      (cong
        (λ terminal →
          Norm.globalNormSq (martingale0 dataSet field)
          + (Norm.globalNormSq (martingale1 dataSet field)
          + (Norm.globalNormSq (martingale2 dataSet field)
          + (Norm.globalNormSq (martingale3 dataSet field) + terminal))))
        (terminalNormZero dataSet field meanZero))
      (ℚRing.solve-∀
        (Norm.globalNormSq (martingale0 dataSet field))
        (Norm.globalNormSq (martingale1 dataSet field))
        (Norm.globalNormSq (martingale2 dataSet field))
        (Norm.globalNormSq (martingale3 dataSet field))))

normalizedFourAxisMartingaleVarianceLevel : ProofLevel
normalizedFourAxisMartingaleVarianceLevel = machineChecked
