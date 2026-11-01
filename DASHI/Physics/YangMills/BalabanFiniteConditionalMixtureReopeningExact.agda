module DASHI.Physics.YangMills.BalabanFiniteConditionalMixtureReopeningExact where

------------------------------------------------------------------------
-- NORMALIZED COARSE LAW + NORMALIZED CONDITIONAL KERNEL
--   -> FINE PROBABILITY LAW + EXACT REOPENING STEP
--
-- Define
--
--   mu_fine(x) = sum_y mu_coarse(y) kappa(y,x).
--
-- If mu_coarse is a finite probability law and every kappa(y,-) is a finite
-- probability law, finite Fubini gives sum_x mu_fine(x)=1.  The reopening
-- disintegration equation is then definitional.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; NonNegative; nonNegative; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanFiniteProbabilityPartitionDisintegrationExact as Finite
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanFiniteRGProbabilityExpectationSemanticsExact as Probability

record FiniteConditionalMixtureData
    (Fine Coarse : Set) : Set₁ where
  field
    fineStates : List Fine
    coarseStates : List Coarse
    project : Fine → Coarse

    coarseWeight : Coarse → ℚ
    coarseWeightNonnegative : ∀ coarse →
      0ℚ ≤ coarseWeight coarse
    coarseWeightNormalized :
      Sums.sumRational coarseStates coarseWeight ≡ 1ℚ

    kernel : Coarse → Fine → ℚ
    kernelNonnegative : ∀ coarse fine →
      0ℚ ≤ kernel coarse fine
    kernelNormalized : ∀ coarse →
      Sums.sumRational fineStates (kernel coarse) ≡ 1ℚ

    FibreSupport : Coarse → Fine → Set
    fibreSupportProjects : ∀ {coarse fine} →
      FibreSupport coarse fine → project fine ≡ coarse
    kernelOffFibreZero : ∀ coarse fine →
      (FibreSupport coarse fine → ⊥) →
      kernel coarse fine ≡ 0ℚ

open FiniteConditionalMixtureData public

fineMixtureWeight :
  ∀ {Fine Coarse} →
  FiniteConditionalMixtureData Fine Coarse →
  Fine → ℚ
fineMixtureWeight dataSet fine =
  Sums.sumRational (coarseStates dataSet)
    (λ coarse →
      coarseWeight dataSet coarse * kernel dataSet coarse fine)

fineMixtureWeightNonnegative :
  ∀ {Fine Coarse}
    (dataSet : FiniteConditionalMixtureData Fine Coarse)
    fine →
  0ℚ ≤ fineMixtureWeight dataSet fine
fineMixtureWeightNonnegative dataSet fine =
  Finite.sumRationalNonnegative
    (coarseStates dataSet)
    (λ coarse →
      coarseWeight dataSet coarse * kernel dataSet coarse fine)
    (λ coarse →
      let
        instance
          coarseNN : NonNegative (coarseWeight dataSet coarse)
          coarseNN = nonNegative
            (coarseWeightNonnegative dataSet coarse)

          kernelNN : NonNegative (kernel dataSet coarse fine)
          kernelNN = nonNegative
            (kernelNonnegative dataSet coarse fine)
      in
      ℚP.nonNegative⁻¹ _)

fineMixtureMassOne :
  ∀ {Fine Coarse}
    (dataSet : FiniteConditionalMixtureData Fine Coarse) →
  Sums.sumRational (fineStates dataSet)
    (fineMixtureWeight dataSet)
  ≡ 1ℚ
fineMixtureMassOne dataSet =
  let
    swap :
      Sums.sumRational (fineStates dataSet)
        (λ fine →
          Sums.sumRational (coarseStates dataSet)
            (λ coarse →
              coarseWeight dataSet coarse * kernel dataSet coarse fine))
      ≡
      Sums.sumRational (coarseStates dataSet)
        (λ coarse →
          Sums.sumRational (fineStates dataSet)
            (λ fine →
              coarseWeight dataSet coarse * kernel dataSet coarse fine))
    swap =
      Fubini.sumSwap
        (fineStates dataSet)
        (coarseStates dataSet)
        (λ fine coarse →
          coarseWeight dataSet coarse * kernel dataSet coarse fine)

    factor :
      Sums.sumRational (coarseStates dataSet)
        (λ coarse →
          Sums.sumRational (fineStates dataSet)
            (λ fine →
              coarseWeight dataSet coarse * kernel dataSet coarse fine))
      ≡
      Sums.sumRational (coarseStates dataSet)
        (λ coarse → coarseWeight dataSet coarse)
    factor =
      Sums.sumRationalCong
        (coarseStates dataSet)
        _
        _
        (λ coarse →
          trans
            (Sums.sumRationalScale
              (coarseWeight dataSet coarse)
              (fineStates dataSet)
              (kernel dataSet coarse))
            (trans
              (cong
                (coarseWeight dataSet coarse *_)
                (kernelNormalized dataSet coarse))
              (ℚP.*-identityʳ (coarseWeight dataSet coarse))))
  in
  trans swap
    (trans factor (coarseWeightNormalized dataSet))

compileConditionalMixtureReopeningStep :
  ∀ {Fine Coarse} →
  FiniteConditionalMixtureData Fine Coarse →
  Reopen.FiniteRGReopeningStep Fine Coarse
compileConditionalMixtureReopeningStep dataSet = record
  { fineStates = fineStates dataSet
  ; coarseStates = coarseStates dataSet
  ; project = project dataSet
  ; fineWeight = fineMixtureWeight dataSet
  ; coarseWeight = coarseWeight dataSet
  ; reopeningKernel = kernel dataSet
  ; FibreSupport = FibreSupport dataSet
  ; fibreSupportProjects = fibreSupportProjects dataSet
  ; reopeningOffFibreZero = kernelOffFibreZero dataSet
  ; reopeningNormalized = kernelNormalized dataSet
  ; disintegrationExact = λ fine → refl
  }

compileConditionalMixtureFineProbabilityLaw :
  ∀ {Fine Coarse}
    (dataSet : FiniteConditionalMixtureData Fine Coarse) →
  Probability.FiniteRGProbabilityLaw
    (compileConditionalMixtureReopeningStep dataSet)
compileConditionalMixtureFineProbabilityLaw dataSet = record
  { fineWeightNonnegative =
      fineMixtureWeightNonnegative dataSet
  ; fineWeightNormalized =
      fineMixtureMassOne dataSet
  }

finiteConditionalMixtureNonnegativeLevel : ProofLevel
finiteConditionalMixtureNonnegativeLevel = machineChecked

finiteConditionalMixtureMassOneLevel : ProofLevel
finiteConditionalMixtureMassOneLevel = machineChecked

finiteConditionalMixtureReopeningCompilerLevel : ProofLevel
finiteConditionalMixtureReopeningCompilerLevel = machineChecked

finiteConditionalMixtureProbabilityCompilerLevel : ProofLevel
finiteConditionalMixtureProbabilityCompilerLevel = machineChecked
