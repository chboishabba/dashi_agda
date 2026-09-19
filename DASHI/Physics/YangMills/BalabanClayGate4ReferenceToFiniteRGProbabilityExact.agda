module DASHI.Physics.YangMills.BalabanClayGate4ReferenceToFiniteRGProbabilityExact where

------------------------------------------------------------------------
-- CANONICAL GATE4 REFERENCE NORMALIZATION -> FINITE RG PROBABILITY LAW
--
-- Gate4 already constructs a normalized selected reference selector from
-- nonnegative raw selected weights, one strictly positive flat configuration,
-- the resulting strictly positive total mass, and a canonical rational
-- reciprocal.
--
-- Its finite-fold algebra is deliberately abstract.  The finite RG probability
-- semantics uses the canonical rational fold sumRational.  This module states
-- only the missing scalar-semantics identification and then derives literal
-- rational nonnegativity and total mass one.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; Positive; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanFiniteRGProbabilityExpectationSemanticsExact as Probability
import DASHI.Physics.YangMills.BalabanClayP3FiniteConstrainedIntegralExact as Integral
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibreNormalizationExact as Reference
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibrePositiveMassExact as PositiveMass
import DASHI.Physics.YangMills.BalabanClayGate4RationalPositiveMassReciprocalExact as Reciprocal
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalReferenceNormalizationExact as Canonical
import DASHI.Physics.YangMills.BalabanClayGate4FlatReferencePositiveWitnessExact as Flat

record RationalReferenceFoldSemantics
    {Scale Fine SlowField Component Functional : Set}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ}
    (canonical :
      Canonical.CanonicalRationalReferenceNormalizationData
        Scale Fine SlowField Component Functional tData) : Set₁ where
  field
    zeroMeaning :
      Integral.zero (T.sumData tData) ≡ 0ℚ

    addMeaning : ∀ left right →
      Integral.add (T.sumData tData) left right ≡ left + right

    nonnegativeMeaning : ∀ {value} →
      PositiveMass.Nonnegative (Canonical.positiveAlgebra canonical) value →
      0ℚ ≤ value

open RationalReferenceFoldSemantics public

foldSelectedIsRationalSum :
  ∀ {Scale Fine SlowField Component Functional}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ}
    {canonical :
      Canonical.CanonicalRationalReferenceNormalizationData
        Scale Fine SlowField Component Functional tData}
    (semantics : RationalReferenceFoldSemantics canonical)
    (selector : Fine → ℚ) slow fields →
  Integral.foldSelected (T.sumData tData) selector slow fields
  ≡ Sums.sumRational fields selector
foldSelectedIsRationalSum semantics selector slow [] =
  zeroMeaning semantics
foldSelectedIsRationalSum {tData = tData} semantics selector slow
  (fine ∷ fields) =
  trans
    (cong
      (Integral.add (T.sumData tData) (selector fine))
      (foldSelectedIsRationalSum semantics selector slow fields))
    (addMeaning semantics
      (selector fine)
      (Sums.sumRational fields selector))

selectedReferenceReciprocal :
  ∀ {Scale Fine SlowField Component Functional}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ}
    (canonical :
      Canonical.CanonicalRationalReferenceNormalizationData
        Scale Fine SlowField Component Functional tData)
    scale component slow →
  Reference.ReciprocalReferenceMass
    (Canonical.referenceAlgebra canonical)
    (Flat.rawSelectedReference
      (Canonical.factors canonical) scale component slow)
    slow
    (T.fastFibre tData scale component)
selectedReferenceReciprocal canonical scale component slow =
  PositiveMass.reciprocalReferenceMassFromPositiveWitness
    (Reciprocal.rationalPositiveMassReciprocalAlgebra
      (Canonical.rationalInterpretation canonical))
    (Canonical.positiveSelectedFibre canonical scale component slow)

selectedReferenceProbabilityWeight :
  ∀ {Scale Fine SlowField Component Functional}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ} →
  (canonical :
    Canonical.CanonicalRationalReferenceNormalizationData
      Scale Fine SlowField Component Functional tData) →
  Scale → Component → SlowField → Fine → ℚ
selectedReferenceProbabilityWeight canonical scale component slow =
  Reference.normalizedReferenceSelector
    (selectedReferenceReciprocal canonical scale component slow)

selectedReferenceMassRationalPositive :
  ∀ {Scale Fine SlowField Component Functional}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ}
    (canonical :
      Canonical.CanonicalRationalReferenceNormalizationData
        Scale Fine SlowField Component Functional tData)
    scale component slow →
  Positive
    (Integral.foldSelected (T.sumData tData)
      (Flat.rawSelectedReference
        (Canonical.factors canonical) scale component slow)
      slow
      (T.fastFibre tData scale component))
selectedReferenceMassRationalPositive canonical scale component slow =
  Reciprocal.positiveMeansRationalPositive
    (Canonical.rationalInterpretation canonical)
    (PositiveMass.selectedReferenceMassPositive
      (Canonical.positiveSelectedFibre canonical scale component slow))

selectedReferenceReciprocalNonnegative :
  ∀ {Scale Fine SlowField Component Functional}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ}
    (canonical :
      Canonical.CanonicalRationalReferenceNormalizationData
        Scale Fine SlowField Component Functional tData)
    scale component slow →
  0ℚ ≤ Reference.reciprocalMass
    (selectedReferenceReciprocal canonical scale component slow)
selectedReferenceReciprocalNonnegative
  {tData = tData} canonical scale component slow =
  Reciprocal.safeRationalReciprocalNonnegative
    (Integral.foldSelected (T.sumData tData)
      (Flat.rawSelectedReference
        (Canonical.factors canonical) scale component slow)
      slow
      (T.fastFibre tData scale component))
    (selectedReferenceMassRationalPositive canonical scale component slow)

selectedReferenceProbabilityWeightNonnegative :
  ∀ {Scale Fine SlowField Component Functional}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ}
    {canonical :
      Canonical.CanonicalRationalReferenceNormalizationData
        Scale Fine SlowField Component Functional tData}
    (semantics : RationalReferenceFoldSemantics canonical)
    scale component slow fine →
  0ℚ ≤ selectedReferenceProbabilityWeight
    canonical scale component slow fine
selectedReferenceProbabilityWeightNonnegative
  {canonical = canonical} semantics scale component slow fine =
  let
    positiveFibre =
      Canonical.positiveSelectedFibre canonical scale component slow

    raw =
      Flat.rawSelectedReference
        (Canonical.factors canonical) scale component slow fine

    reciprocal =
      Reference.reciprocalMass
        (selectedReferenceReciprocal canonical scale component slow)

    rawNN : 0ℚ ≤ raw
    rawNN =
      nonnegativeMeaning semantics
        (PositiveMass.selectedWeightNonnegative positiveFibre fine)

    reciprocalNN : 0ℚ ≤ reciprocal
    reciprocalNN =
      selectedReferenceReciprocalNonnegative
        canonical scale component slow

    instance
      reciprocalNNI : NonNegative reciprocal
      reciprocalNNI = nonNegative reciprocalNN

      rawNNI : NonNegative raw
      rawNNI = nonNegative rawNN

    productNN : 0ℚ ≤ reciprocal * raw
    productNN = ℚP.nonNegative⁻¹ _
  in
  subst
    (λ value → 0ℚ ≤ value)
    (sym
      (Reciprocal.multiplyMeaning
        (Canonical.rationalInterpretation canonical)
        reciprocal raw))
    productNN

selectedReferenceProbabilityMassOne :
  ∀ {Scale Fine SlowField Component Functional}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ}
    {canonical :
      Canonical.CanonicalRationalReferenceNormalizationData
        Scale Fine SlowField Component Functional tData}
    (semantics : RationalReferenceFoldSemantics canonical)
    scale component slow →
  Sums.sumRational
    (T.fastFibre tData scale component)
    (selectedReferenceProbabilityWeight canonical scale component slow)
  ≡ 1ℚ
selectedReferenceProbabilityMassOne
  {tData = tData} {canonical = canonical}
  semantics scale component slow =
  let
    reciprocal =
      selectedReferenceReciprocal canonical scale component slow

    foldAsSum =
      foldSelectedIsRationalSum semantics
        (selectedReferenceProbabilityWeight canonical scale component slow)
        slow
        (T.fastFibre tData scale component)

    normalized =
      Reference.normalizedReferenceMassExact reciprocal

    oneIsOne =
      Reciprocal.oneMeaning
        (Canonical.rationalInterpretation canonical)
  in
  trans
    (sym foldAsSum)
    (trans normalized oneIsOne)

record NormalizedReferenceReopeningWeld
    {Scale Fine SlowField Component Functional Coarse : Set}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ}
    {canonical :
      Canonical.CanonicalRationalReferenceNormalizationData
        Scale Fine SlowField Component Functional tData}
    (semantics : RationalReferenceFoldSemantics canonical)
    (step : Reopen.FiniteRGReopeningStep Fine Coarse) : Set₁ where
  field
    scale : Scale
    component : Component
    slow : SlowField

    fineStatesAreSelectedFastFibre :
      Reopen.fineStates step
      ≡ T.fastFibre tData scale component

    fineWeightIsNormalizedReference : ∀ fine →
      Reopen.fineWeight step fine
      ≡ selectedReferenceProbabilityWeight
          canonical scale component slow fine

open NormalizedReferenceReopeningWeld public

compileNormalizedReferenceProbabilityLaw :
  ∀ {Scale Fine SlowField Component Functional Coarse}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ}
    {canonical :
      Canonical.CanonicalRationalReferenceNormalizationData
        Scale Fine SlowField Component Functional tData}
    {semantics : RationalReferenceFoldSemantics canonical}
    {step : Reopen.FiniteRGReopeningStep Fine Coarse} →
  NormalizedReferenceReopeningWeld semantics step →
  Probability.FiniteRGProbabilityLaw step
compileNormalizedReferenceProbabilityLaw
  {canonical = canonical} {semantics = semantics} {step = step} weld = record
  { fineWeightNonnegative = λ fine →
      subst
        (λ weight → 0ℚ ≤ weight)
        (sym (fineWeightIsNormalizedReference weld fine))
        (selectedReferenceProbabilityWeightNonnegative
          semantics (scale weld) (component weld) (slow weld) fine)

  ; fineWeightNormalized =
      trans
        (Sums.sumRationalCong
          (Reopen.fineStates step)
          (Reopen.fineWeight step)
          (selectedReferenceProbabilityWeight
            canonical (scale weld) (component weld) (slow weld))
          (fineWeightIsNormalizedReference weld))
        (trans
          (cong
            (λ fields →
              Sums.sumRational fields
                (selectedReferenceProbabilityWeight
                  canonical (scale weld) (component weld) (slow weld)))
            (fineStatesAreSelectedFastFibre weld))
          (selectedReferenceProbabilityMassOne
            semantics (scale weld) (component weld) (slow weld)))
  }

rationalReferenceFoldCompilerLevel : ProofLevel
rationalReferenceFoldCompilerLevel = machineChecked

normalizedReferenceProbabilityWeightLevel : ProofLevel
normalizedReferenceProbabilityWeightLevel = machineChecked

normalizedReferenceToFiniteRGProbabilityCompilerLevel : ProofLevel
normalizedReferenceToFiniteRGProbabilityCompilerLevel = machineChecked

rationalReferenceFoldSemanticsLevel : ProofLevel
rationalReferenceFoldSemanticsLevel = conditional

normalizedReferenceReopeningSameObjectLevel : ProofLevel
normalizedReferenceReopeningSameObjectLevel = conditional


------------------------------------------------------------------------
-- Lift the pointwise Gate4/reopening weld over every selected cutoff.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanFiniteVolumeReopeningPresentationRound283Exact as R283
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5

record Gate4SelectedProbabilityPresentationInputs
    {Scale Fine SlowField Component Functional Coarse Measure : Set}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ}
    {canonical :
      Canonical.CanonicalRationalReferenceNormalizationData
        Scale Fine SlowField Component Functional tData}
    (semantics : RationalReferenceFoldSemantics canonical)
    (thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ)
    (presentation :
      R283.FiniteVolumeReopeningPresentation
        Measure Fine Coarse thermodynamic) : Set₁ where
  field
    normalizedReferenceWeldAt : ∀ cutoff →
      NormalizedReferenceReopeningWeld
        semantics
        (R283.stepAt presentation cutoff)

open Gate4SelectedProbabilityPresentationInputs public

compileGate4SelectedT5FiniteProbabilityPresentation :
  ∀ {Scale Fine SlowField Component Functional Coarse Measure}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ}
    {canonical :
      Canonical.CanonicalRationalReferenceNormalizationData
        Scale Fine SlowField Component Functional tData}
    {semantics : RationalReferenceFoldSemantics canonical}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ}
    {presentation :
      R283.FiniteVolumeReopeningPresentation
        Measure Fine Coarse thermodynamic} →
  Gate4SelectedProbabilityPresentationInputs
    semantics thermodynamic presentation →
  Probability.SelectedT5FiniteProbabilityPresentation
    Measure Fine Coarse thermodynamic
compileGate4SelectedT5FiniteProbabilityPresentation
  {presentation = presentation} inputs = record
  { presentation = presentation
  ; probabilityAt = λ cutoff →
      compileNormalizedReferenceProbabilityLaw
        (normalizedReferenceWeldAt inputs cutoff)
  }

gate4SelectedT5ProbabilityPresentationCompilerLevel : ProofLevel
gate4SelectedT5ProbabilityPresentationCompilerLevel = machineChecked
