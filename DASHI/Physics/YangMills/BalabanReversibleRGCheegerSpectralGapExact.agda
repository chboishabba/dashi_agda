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
-- Keep the hard theorem boundary honest.  Lawler--Sokal supplies the standard
-- conductance/isoperimetry -> L^2 spectral-gap bridge for Markov chains and
-- Markov processes.  We do NOT request a spectral gap as a primitive physical
-- field.  Instead, a physical RG construction must produce a reversible
-- positive Markov object and its conductance.  This file proves the exact
-- rational normalization used downstream from the denominator-cleared
-- Cheeger inequality phi^2 <= 2 gamma.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

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

cheegerRationalNormalizationLevel : ProofLevel
cheegerRationalNormalizationLevel = machineChecked

-- These are the actual physical producer leaves.  Without them, the imported
-- theorem says nothing about Yang--Mills.
literalRGReversibilityLevel : ProofLevel
literalRGReversibilityLevel = conditional

cutoffUniformRGConductanceLowerBoundLevel : ProofLevel
cutoffUniformRGConductanceLowerBoundLevel = conditional
