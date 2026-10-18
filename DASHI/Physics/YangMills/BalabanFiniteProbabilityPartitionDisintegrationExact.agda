module DASHI.Physics.YangMills.BalabanFiniteProbabilityPartitionDisintegrationExact where

------------------------------------------------------------------------
-- FINITE WEIGHTED LAW + COARSE PARTITION -> NORMALIZED REOPENING KERNEL
--
-- Let mu be nonnegative finite rational weights on an explicit fine-state list.
-- A finite coarse partition is represented by Boolean masks chi_y(x).
--
--   mu_Y(y)    = sum_x chi_y(x) mu(x)
--   kappa(y,x) = mu_Y(y)^(-1) chi_y(x) mu(x).
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
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; Positive; NonNegative; nonNegative; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanClayGate4RationalPositiveMassReciprocalExact as Reciprocal
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibrePositiveMassExact as PositiveMass

indicator : Bool → ℚ
indicator true = 1ℚ
indicator false = 0ℚ

record FiniteCoarsePartition
    {Fine Coarse : Set}
    (states : List Fine)
    (fineWeight : Fine → ℚ) : Set₁ where
  field
    coarseStates : List Coarse
    project : Fine → Coarse
    matches : Coarse → Fine → Bool

    Match : Coarse → Fine → Set
    matchTrue : ∀ coarse fine →
      matches coarse fine ≡ true → Match coarse fine
    matchProjects : ∀ {coarse fine} →
      Match coarse fine → project fine ≡ coarse

    -- Coverage + uniqueness of the listed coarse fibres, encoded exactly in Q.
    partitionOfUnity : ∀ fine →
      Sums.sumRational coarseStates
        (λ coarse → indicator (matches coarse fine))
      ≡ 1ℚ

    -- Zero-mass coarse fibres are omitted from the selected coarse list.
    coarseFibreMassPositive : ∀ coarse →
      Positive
        (Sums.sumRational states
          (λ fine →
            indicator (matches coarse fine) * fineWeight fine))

open FiniteCoarsePartition public

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
  ⊥-elim (noMatch (matchTrue partition coarse fine refl))
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

    rearrange :
      mass * (inv * masked) ≡ (inv * mass) * masked
    rearrange = ℚRing.solve-∀ mass inv masked

    cancel : inv * mass ≡ 1ℚ
    cancel = coarseMassReciprocalTimesMass partition coarse
  in
  trans rearrange
    (trans
      (cong (λ value → value * masked) cancel)
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
    commute :
      Sums.sumRational (coarseStates partition)
        (λ coarse →
          indicator (matches partition coarse fine) * fineWeight fine)
      ≡
      Sums.sumRational (coarseStates partition)
        (λ coarse →
          fineWeight fine * indicator (matches partition coarse fine))
    commute =
      Sums.sumRationalCong
        (coarseStates partition)
        _
        _
        (λ coarse →
          ℚP.*-comm
            (indicator (matches partition coarse fine))
            (fineWeight fine))

    factor :
      Sums.sumRational (coarseStates partition)
        (λ coarse →
          fineWeight fine * indicator (matches partition coarse fine))
      ≡
      fineWeight fine
        * Sums.sumRational (coarseStates partition)
            (λ coarse → indicator (matches partition coarse fine))
    factor =
      Sums.sumRationalScale
        (fineWeight fine)
        (coarseStates partition)
        (λ coarse → indicator (matches partition coarse fine))

    one = partitionOfUnity partition fine
  in
  trans commute
    (trans factor
      (trans
        (cong (λ value → fineWeight fine * value) one)
        (ℚP.*-identityʳ (fineWeight fine))))

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
  FiniteCoarsePartition states fineWeight →
  Reopen.FiniteRGReopeningStep Fine Coarse
compileFiniteRGReopeningStep {states = states} {fineWeight = fineWeight}
  partition = record
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



------------------------------------------------------------------------
-- Positive coarse-fibre mass from a literal positive fine witness.
------------------------------------------------------------------------

sumRationalNonnegative :
  ∀ {A : Set} (values : List A) (term : A → ℚ) →
  (∀ value → 0ℚ ≤ term value) →
  0ℚ ≤ Sums.sumRational values term
sumRationalNonnegative [] term pointwise = ℚP.≤-refl
sumRationalNonnegative (value ∷ values) term pointwise =
  ℚP.+-mono-≤
    (pointwise value)
    (sumRationalNonnegative values term pointwise)

sumRationalPositiveAtMember :
  ∀ {A : Set} (values : List A) (term : A → ℚ) witness →
  PositiveMass._∈_ witness values →
  (∀ value → 0ℚ ≤ term value) →
  Positive (term witness) →
  Positive (Sums.sumRational values term)
sumRationalPositiveAtMember [] term witness () pointwise positive
sumRationalPositiveAtMember (.witness ∷ values) term witness
  PositiveMass.here pointwise positive =
  let
    restNN =
      sumRationalNonnegative values term pointwise
    raw :
      0ℚ + 0ℚ
      <
      term witness + Sums.sumRational values term
    raw =
      ℚP.+-mono-<-≤ positive restNN
  in
  subst
    (λ lower →
      lower < term witness + Sums.sumRational values term)
    (ℚRing.solve [])
    raw
sumRationalPositiveAtMember (value ∷ values) term witness
  (PositiveMass.there membership) pointwise positive =
  let
    headNN = pointwise value
    tailPositive =
      sumRationalPositiveAtMember
        values term witness membership pointwise positive
    raw :
      0ℚ + 0ℚ
      <
      term value + Sums.sumRational values term
    raw =
      ℚP.+-mono-≤-< headNN tailPositive
  in
  subst
    (λ lower →
      lower < term value + Sums.sumRational values term)
    (ℚRing.solve [])
    raw

record FiniteCoarsePartitionWitness
    {Fine Coarse : Set}
    (states : List Fine)
    (fineWeight : Fine → ℚ) : Set₁ where
  field
    coarseStates : List Coarse
    project : Fine → Coarse
    matches : Coarse → Fine → Bool

    Match : Coarse → Fine → Set
    matchTrue : ∀ coarse fine →
      matches coarse fine ≡ true → Match coarse fine
    matchProjects : ∀ {coarse fine} →
      Match coarse fine → project fine ≡ coarse

    partitionOfUnity : ∀ fine →
      Sums.sumRational coarseStates
        (λ coarse → indicator (matches coarse fine))
      ≡ 1ℚ

    fineWeightNonnegative : ∀ fine →
      0ℚ ≤ fineWeight fine

    positiveWitness : Coarse → Fine
    positiveWitnessInStates : ∀ coarse →
      PositiveMass._∈_ (positiveWitness coarse) states
    positiveWitnessMatches : ∀ coarse →
      matches coarse (positiveWitness coarse) ≡ true
    positiveWitnessWeight : ∀ coarse →
      Positive (fineWeight (positiveWitness coarse))

open FiniteCoarsePartitionWitness public

maskedFineWeightNonnegativeFromWitness :
  ∀ {Fine Coarse}
    {states : List Fine}
    {fineWeight : Fine → ℚ}
    (witnessData : FiniteCoarsePartitionWitness states fineWeight)
    coarse fine →
  0ℚ ≤
    indicator (FiniteCoarsePartitionWitness.matches witnessData coarse fine)
      * fineWeight fine
maskedFineWeightNonnegativeFromWitness witnessData coarse fine
  with FiniteCoarsePartitionWitness.matches witnessData coarse fine
... | true =
  subst
    (λ value → 0ℚ ≤ value)
    (sym (ℚP.*-identityˡ (fineWeight fine)))
    (FiniteCoarsePartitionWitness.fineWeightNonnegative witnessData fine)
... | false = ℚP.≤-refl

coarseFibreMassPositiveFromWitness :
  ∀ {Fine Coarse}
    {states : List Fine}
    {fineWeight : Fine → ℚ}
    (witnessData : FiniteCoarsePartitionWitness states fineWeight)
    coarse →
  Positive
    (Sums.sumRational states
      (λ fine →
        indicator
          (FiniteCoarsePartitionWitness.matches witnessData coarse fine)
        * fineWeight fine))
coarseFibreMassPositiveFromWitness
  {states = states} {fineWeight = fineWeight}
  witnessData coarse =
  let
    witness =
      FiniteCoarsePartitionWitness.positiveWitness witnessData coarse

    witnessMembership =
      FiniteCoarsePartitionWitness.positiveWitnessInStates
        witnessData coarse

    pointwise =
      maskedFineWeightNonnegativeFromWitness witnessData coarse

    witnessTermPositive :
      Positive
        (indicator
          (FiniteCoarsePartitionWitness.matches witnessData coarse witness)
          * fineWeight witness)
    witnessTermPositive
      rewrite
        FiniteCoarsePartitionWitness.positiveWitnessMatches
          witnessData coarse =
      subst
        Positive
        (sym (ℚP.*-identityˡ (fineWeight witness)))
        (FiniteCoarsePartitionWitness.positiveWitnessWeight
          witnessData coarse)
  in
  sumRationalPositiveAtMember
    states
    (λ fine →
      indicator
        (FiniteCoarsePartitionWitness.matches witnessData coarse fine)
      * fineWeight fine)
    witness
    witnessMembership
    pointwise
    witnessTermPositive

compileFiniteCoarsePartition :
  ∀ {Fine Coarse}
    {states : List Fine}
    {fineWeight : Fine → ℚ} →
  FiniteCoarsePartitionWitness states fineWeight →
  FiniteCoarsePartition states fineWeight
compileFiniteCoarsePartition witnessData = record
  { coarseStates =
      FiniteCoarsePartitionWitness.coarseStates witnessData
  ; project =
      FiniteCoarsePartitionWitness.project witnessData
  ; matches =
      FiniteCoarsePartitionWitness.matches witnessData
  ; Match =
      FiniteCoarsePartitionWitness.Match witnessData
  ; matchTrue =
      FiniteCoarsePartitionWitness.matchTrue witnessData
  ; matchProjects =
      FiniteCoarsePartitionWitness.matchProjects witnessData
  ; partitionOfUnity =
      FiniteCoarsePartitionWitness.partitionOfUnity witnessData
  ; coarseFibreMassPositive =
      coarseFibreMassPositiveFromWitness witnessData
  }

finiteCoarseFibrePositiveWitnessCompilerLevel : ProofLevel
finiteCoarseFibrePositiveWitnessCompilerLevel = machineChecked

finitePartitionConditionalKernelLevel : ProofLevel
finitePartitionConditionalKernelLevel = machineChecked

finitePartitionKernelNormalizationLevel : ProofLevel
finitePartitionKernelNormalizationLevel = machineChecked

finitePartitionDisintegrationLevel : ProofLevel
finitePartitionDisintegrationLevel = machineChecked

finitePartitionReopeningCompilerLevel : ProofLevel
finitePartitionReopeningCompilerLevel = machineChecked
