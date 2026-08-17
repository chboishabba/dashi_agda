module DASHI.Physics.YangMills.BalabanReversibleRGCheegerSpectralGapExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Gregory F. Lawler and Alan D. Sokal,
-- "Bounds on the L^2 Spectrum for Markov Chains and Markov Processes:
-- A Generalization of Cheeger's Inequality",
-- Transactions of the American Mathematical Society 309 (1988), 557--580.
-- DOI: 10.1090/S0002-9947-1988-0930082-9.
--
-- DASHI CONTRIBUTION
--
-- Keep the hard theorem boundary honest.  Lawler--Sokal treats discrete-time
-- Markov chains and continuous-time Markovian jump processes on general state
-- spaces in reversible AND nonreversible settings, and also gives a killed-
-- process version.  Therefore detailed balance is not a mandatory physical
-- Yang--Mills producer.  The actual obligation is to construct the literal RG
-- kernel and prove the hypotheses of whichever Lawler--Sokal regime it really
-- inhabits.
--
-- The rational calculation below remains the clean reversible/two-sided
-- normalization used when that specialization applies:
--
--   phi^2 <= 2 gamma  ==>  (1/2) phi^2 <= gamma.
--
-- No spectral gap is requested as an independent physical receipt.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

------------------------------------------------------------------------
-- The three theorem regimes relevant to the literal RG producer.
------------------------------------------------------------------------

data LawlerSokalKernelRegime : Set where
  reversible nonreversible killed : LawlerSokalKernelRegime

record LiteralRGLawlerSokalRegime : Set where
  field
    regime : LawlerSokalKernelRegime
    positiveMarkovKernelConstructed : Set
    theoremHypothesesForChosenRegime : Set
open LiteralRGLawlerSokalRegime public

record ReversibleRGCheegerData : Set where
  field
    conductance : ℚ
    spectralGap : ℚ
    conductanceNonnegative : 0ℚ ≤ conductance
    spectralGapNonnegative : 0ℚ ≤ spectralGap
    lawlerSokalLowerDenominatorCleared :
      conductance * conductance ≤ (+ 2 / 1) * spectralGap
open ReversibleRGCheegerData public

cheegerLowerBoundNormalized :
  ∀ data →
  (+ 1 / 2) * (conductance data * conductance data)
  ≤ spectralGap data
cheegerLowerBoundNormalized data =
  let
    scaled =
      Norm.scaleNonnegative
        (+ 1 / 2)
        (ℚP.nonNegative⁻¹ (+ 1 / 2))
        (lawlerSokalLowerDenominatorCleared data)
  in
  subst
    (λ right →
      (+ 1 / 2) * (conductance data * conductance data) ≤ right)
    (ℚRing.solve-∀ (spectralGap data))
    scaled

record ReversibleRGCheegerTwoSidedData : Set where
  field
    lowerData : ReversibleRGCheegerData
    lawlerSokalUpper :
      spectralGap lowerData ≤ (+ 2 / 1) * conductance lowerData
open ReversibleRGCheegerTwoSidedData public

cheegerTwoSided :
  ∀ data →
  ((+ 1 / 2) *
    (conductance (lowerData data) * conductance (lowerData data))
    ≤ spectralGap (lowerData data))
  ×
  (spectralGap (lowerData data)
    ≤ (+ 2 / 1) * conductance (lowerData data))
cheegerTwoSided data =
  cheegerLowerBoundNormalized (lowerData data) , lawlerSokalUpper data

lawlerSokalCheegerTheoremLevel : ProofLevel
lawlerSokalCheegerTheoremLevel = standardImported

lawlerSokalNonreversibleAndKilledRegimesLevel : ProofLevel
lawlerSokalNonreversibleAndKilledRegimesLevel = standardImported

cheegerRationalNormalizationLevel : ProofLevel
cheegerRationalNormalizationLevel = machineChecked

-- Physical leaves: construct the SAME literal Bałaban RG kernel as a positive
-- Markov object, classify the regime it actually satisfies, prove the
-- corresponding theorem hypotheses, and then obtain a cutoff-uniform
-- conductance/isoperimetric lower bound.  Reversibility is only one possible
-- regime, not a required conclusion.
literalRGPositiveMarkovKernelLevel : ProofLevel
literalRGPositiveMarkovKernelLevel = conditional

literalRGLawlerSokalChosenRegimeHypothesesLevel : ProofLevel
literalRGLawlerSokalChosenRegimeHypothesesLevel = conditional

cutoffUniformRGConductanceLowerBoundLevel : ProofLevel
cutoffUniformRGConductanceLowerBoundLevel = conditional
