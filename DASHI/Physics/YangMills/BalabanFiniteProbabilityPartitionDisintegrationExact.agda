module DASHI.Physics.YangMills.BalabanFiniteProbabilityPartitionDisintegrationExact where

------------------------------------------------------------------------
-- FINITE PROBABILITY LAW + COARSE PARTITION -> NORMALIZED REOPENING KERNEL
--
-- Let mu be a finite rational probability law on an explicit fine-state list.
-- A finite coarse partition is represented by Boolean masks chi_y(x).
--
--   mu_Y(y)   = sum_x chi_y(x) mu(x)
--   kappa(y,x)= mu_Y(y)^(-1) chi_y(x) mu(x).
--
-- If every listed coarse fibre has strictly positive mass and the masks form a
-- partition of unity on each fine state, then:
--
--   sum_x kappa(y,x) = 1
--   mu(x) = sum_y mu_Y(y) kappa(y,x).
--
-- This is exact finite rational algebra.  No analytic disintegration theorem
-- and no probability postulate are used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; Positive; NonNegative; nonNegative; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteRationalOrderCoreExact as Order
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanFiniteRGProbabilityExpectationSemanticsExact as Probability
import DASHI.Physics.YangMills.BalabanClayGate4RationalPositiveMassReciprocalExact as Reciprocal

record FiniteCoarsePartition
    {Fine Coarse : Set}
    (stepStates : List Fine)
    (fineWeight : Fine → ℚ) : Set₁ where
  field
    coarseStates : List Coarse
    project : Fine → Coarse
    matches : Coarse → Fine → Bool

    Match : Coarse → Fine → Set
    matchTrue : ∀ coarse fine →
      matches coarse fine ≡ true → Match coarse fine
    matchFalse : ∀ coarse fine →
      matches coarse fine ≡ false → Match coarse fine → ⊥

    matchProjects : ∀ {coarse fine} →
      Match coarse fine → project fine ≡ coarse

    -- Exact finite partition-of-unity receipt.  This simultaneously encodes
    -- coverage and uniqueness of the listed coarse fibres.
    partitionOfUnity : ∀ fine →
      Sums.sumRational coarseStates
        (λ coarse → indicator (matches coarse fine))
      ≡ 1ℚ

    -- Every listed coarse fibre has positive probability mass.  Zero-mass
    -- coarse states should be omitted from the selected coarse list.
    coarseFibreMassPositive : ∀ coarse →
      Positive
        (Sums.sumRational stepStates
          (λ fine →
            indicator (matches coarse fine) * fineWeight fine))

  where
  indicator : Bool → ℚ
  indicator true = 1ℚ
  indicator false = 0ℚ

open FiniteCoarsePartition public

indicator : Bool → ℚ
indicator true = 1ℚ
indicator false = 0ℚ

maskedFineWeight :
  ∀ {Fine Coarse}
    {states : List Fine}
    {fineWeight : Fine → ℚ} →
  FiniteCoarsePartition states fineWeight →
  Coarse → Fine → ℚ
maskedFineWeight partition coarse fine =
  indicator (matches partition coarse fine) * fineWeight fine

coarseMass :
  ∀ {Fine Coarse}
    {states : List Fine}
    {fineWeight : Fine → ℚ} →
  FiniteCoarsePartition states fineWeight →
  Coarse → ℚ
coarseMass {states = states} partition coarse =
  Sums.sumRational states (maskedFineWeight partition coarse)

coarseMassPositive :
  ∀ {Fine Coarse}
    {states : List Fine}
    {fineWeight : Fine → ℚ}
    (partition : FiniteCoarsePartition states fineWeight)
    coarse →
  Positive (coarseMass partition coarse)
coarseMassPositive = coarseFibreMassPositive

coarseMassReciprocal :
  ∀ {Fine Coarse}
    {states : List Fine}
    {fineWeight : Fine → ℚ} →
  FiniteCoarsePartition states fineWeight →
  Coarse → ℚ
coarseMassReciprocal partition coarse =
  Reciprocal.safeRationalReciprocal (coarseMass partition coarse)

coarseMassReciprocalTimesMass :
  ∀ {Fine Coarse}
    {states : List Fine}
    {fineWeight : Fine → ℚ}
    (partition : FiniteCoarsePartition states fineWeight)
    coarse →
  coarseMassReciprocal partition coarse
    * coarseMass partition coarse
  ≡ 1ℚ
coarseMassReciprocalTimesMass partition coarse =
  Reciprocal.safeRationalReciprocalTimesPositive
    (coarseMass partition coarse)
    (coarseMassPositive partition coarse)

conditionalKernel :
  ∀ {Fine Coarse}
    {states : List Fine}
    {fineWeight : Fine → ℚ} →
  FiniteCoarsePartition states fineWeight →
  Coarse → Fine → ℚ
conditionalKernel partition coarse fine =
  coarseMassReciprocal partition coarse
  * maskedFineWeight partition coarse fine

conditionalKernelOffFibreZero :
  ∀ {Fine Coarse}
    {states : List Fine}
    {fineWeight : Fine → ℚ}
    (partition : FiniteCoarsePartition states fineWeight)
    coarse fine →
  (Match partition coarse fine → ⊥) →
  conditionalKernel partition coarse fine ≡ 0ℚ
conditionalKernelOffFibreZero partition coarse fine noMatch
  with matches partition coarse fine
... | true =
  let
    impossible =
      noMatch (matchTrue partition coarse fine refl)
  in
  ⊥-elim impossible
... | false =
  ℚRing.solve-∀
    (coarseMassReciprocal partition coarse)
    (fineWeight fine)

conditionalKernelNormalized :
  ∀ {Fine Coarse}
    {states : List Fine}
    {fineWeight : Fine → ℚ}
    (partition : FiniteCoarsePartition states fineWeight)
    coarse →
  Sums.sumRational states
    (conditionalKernel partition coarse)
  ≡ 1ℚ
conditionalKernelNormalized {states = states} partition coarse =
  trans
    (Sums.sumRationalScale
      (coarseMassReciprocal partition coarse)
      states
      (maskedFineWeight partition coarse))
    (coarseMassReciprocalTimesMass partition coarse)

coarseTimesConditionalPointwise :
  ∀ {Fine Coarse}
    {states : List Fine}
    {fineWeight : Fine → ℚ}
    (partition : FiniteCoarsePartition states fineWeight)
    coarse fine →
  coarseMass partition coarse
    * conditionalKernel partition coarse fine
  ≡ maskedFineWeight partition coarse fine
coarseTimesConditionalPointwise partition coarse fine =
  let
    mass = coarseMass partition coarse
    inv = coarseMassReciprocal partition coarse
    masked = maskedFineWeight partition coarse fine
    cancel : inv * mass ≡ 1ℚ
    cancel = coarseMassReciprocalTimesMass partition coarse
  in
  trans
    (ℚRing.solve-∀ mass inv masked)
    (trans
      (cong (_* masked) cancel)
      (ℚP.*-identityˡ masked))

sumMaskedAcrossCoarse :
  ∀ {Fine Coarse}
    {states : List Fine}
    {fineWeight : Fine → ℚ}
    (partition : FiniteCoarsePartition states fineWeight)
    fine →
  Sums.sumRational (coarseStates partition)
    (λ coarse → maskedFineWeight partition coarse fine)
  ≡ fineWeight fine
sumMaskedAcrossCoarse partition fine =
  let
    distribute :
      Sums.sumRational (coarseStates partition)
        (λ coarse →
          indicator (matches partition coarse fine) * fineWeight fine)
      ≡
      Sums.sumRational (coarseStates partition)
        (λ coarse → indicator (matches partition coarse fine))
        * fineWeight fine
    distribute =
      trans
        (Sums.sumRationalCong
          (coarseStates partition)
          (λ coarse →
            indicator (matches partition coarse fine) * fineWeight fine)
          (λ coarse →
            fineWeight fine * indicator (matches partition coarse fine))
          (λ coarse →
            ℚP.*-comm
              (indicator (matches partition coarse fine))
              (fineWeight fine)))
        (Sums.sumRationalScale
          (fineWeight fine)
          (coarseStates partition)
          (λ coarse → indicator (matches partition coarse fine)))

    one =
      partitionOfUnity partition fine
  in
  trans distribute
    (trans
      (cong (_* fineWeight fine) one)
      (ℚP.*-identityˡ (fineWeight fine)))

conditionalDisintegrationExact :
  ∀ {Fine Coarse}
    {states : List Fine}
    {fineWeight : Fine → ℚ}
    (partition : FiniteCoarsePartition states fineWeight)
    fine →
  fineWeight fine
  ≡
  Sums.sumRational (coarseStates partition)
    (λ coarse →
      coarseMass partition coarse
      * conditionalKernel partition coarse fine)
conditionalDisintegrationExact partition fine =
  sym
    (trans
      (Sums.sumRationalCong
        (coarseStates partition)
        (λ coarse →
          coarseMass partition coarse
          * conditionalKernel partition coarse fine)
        (λ coarse → maskedFineWeight partition coarse fine)
        (λ coarse →
          coarseTimesConditionalPointwise partition coarse fine))
      (sumMaskedAcrossCoarse partition fine))

compileFiniteRGReopeningStep :
  ∀ {Fine Coarse}
    {states : List Fine}
    {fineWeight : Fine → ℚ} →
  Probability.FiniteRGProbabilityLaw
    (dummyFineStep states fineWeight) →
  (partition : FiniteCoarsePartition states fineWeight) →
  Reopen.FiniteRGReopeningStep Fine Coarse
compileFiniteRGReopeningStep {states = states} {fineWeight = fineWeight}
  probability partition = record
  { fineStates = states
  ; coarseStates = coarseStates partition
  ; project = project partition
  ; fineWeight = fineWeight
  ; coarseWeight = coarseMass partition
  ; reopeningKernel = conditionalKernel partition
  ; FibreSupport = Match partition
  ; fibreSupportProjects = matchProjects partition
  ; reopeningOffFibreZero =
      conditionalKernelOffFibreZero partition
  ; reopeningNormalized =
      conditionalKernelNormalized partition
  ; disintegrationExact =
      conditionalDisintegrationExact partition
  }
  where
  dummyFineStep :
    List Fine → (Fine → ℚ) →
    Reopen.FiniteRGReopeningStep Fine Fine
  dummyFineStep states fineWeight = record
    { fineStates = states
    ; coarseStates = states
    ; project = λ fine → fine
    ; fineWeight = fineWeight
    ; coarseWeight = fineWeight
    ; reopeningKernel = λ _ _ → 0ℚ
    ; FibreSupport = λ _ _ → ⊥
    ; fibreSupportProjects = λ ()
    ; reopeningOffFibreZero = λ _ _ _ → refl
    ; reopeningNormalized = λ _ → refl
    ; disintegrationExact = λ _ → refl
    }

finitePartitionConditionalKernelLevel : ProofLevel
finitePartitionConditionalKernelLevel = machineChecked

finitePartitionKernelNormalizationLevel : ProofLevel
finitePartitionKernelNormalizationLevel = machineChecked

finitePartitionDisintegrationLevel : ProofLevel
finitePartitionDisintegrationLevel = machineChecked
