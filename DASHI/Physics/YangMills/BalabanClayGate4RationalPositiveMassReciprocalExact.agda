module DASHI.Physics.YangMills.BalabanClayGate4RationalPositiveMassReciprocalExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; Positive; _*_; 1/_; _≟_; ≢-nonZero)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)
open import Relation.Nullary using (yes; no)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayP3FiniteConstrainedIntegralExact as Integral
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibreNormalizationExact as Reference
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibrePositiveMassExact as PositiveMass

------------------------------------------------------------------------
-- Constructive arithmetic provenance.
--
-- Errett Bishop and Douglas Bridges,
-- "Constructive Analysis", Springer (1985).
-- DOI: 10.1007/978-3-642-61667-9.
--
-- Agda standard library, Data.Rational.Base and Data.Rational.Properties:
-- decidable zero, `≢-nonZero`, proof-indexed reciprocal, `pos⇒nonZero`, and
-- `*-inverseˡ`. No independent DOI is assigned to the library module.
--
-- The total function below returns zero at zero solely to meet DASHI's existing
-- total-function record. Its inverse law is stated only on positive inputs, so
-- the zero branch is eliminated and no division-by-zero theorem is asserted.
------------------------------------------------------------------------

data Empty : Set where

emptyEliminate : ∀ {A : Set} → Empty → A
emptyEliminate ()

positiveZeroImpossible : Positive 0ℚ → Empty
positiveZeroImpossible ()

safeRationalReciprocal : ℚ → ℚ
safeRationalReciprocal value with value ≟ 0ℚ
... | yes _ = 0ℚ
... | no value≢zero = (1/ value) {{≢-nonZero value≢zero}}

safeRationalReciprocalTimesPositive :
  ∀ (value : ℚ) → Positive value →
  safeRationalReciprocal value * value ≡ 1ℚ
safeRationalReciprocalTimesPositive value positive with value ≟ 0ℚ
... | yes value≡zero =
  emptyEliminate
    (positiveZeroImpossible (subst Positive value≡zero positive))
... | no value≢zero =
  ℚP.*-inverseˡ value {{≢-nonZero value≢zero}}

record RationalPositiveMassInterpretation
    {Fine SlowField : Set}
    {sumData : Integral.FiniteConstrainedSum Fine SlowField ℚ}
    (referenceAlgebra : Reference.FiniteReferenceFibreAlgebra sumData)
    (positiveAlgebra : PositiveMass.PositiveFiniteFoldAlgebra sumData) : Set₁ where
  field
    positiveMeansRationalPositive : ∀ {value : ℚ} →
      PositiveMass.Positive positiveAlgebra value → Positive value

    multiplyMeaning : ∀ (left right : ℚ) →
      Reference.multiply referenceAlgebra left right ≡ left * right

    oneMeaning : Reference.one referenceAlgebra ≡ 1ℚ

open RationalPositiveMassInterpretation public

rationalPositiveMassReciprocalAlgebra :
  ∀ {Fine SlowField}
    {sumData : Integral.FiniteConstrainedSum Fine SlowField ℚ}
    {referenceAlgebra : Reference.FiniteReferenceFibreAlgebra sumData}
    {positiveAlgebra : PositiveMass.PositiveFiniteFoldAlgebra sumData} →
  RationalPositiveMassInterpretation referenceAlgebra positiveAlgebra →
  PositiveMass.PositiveMassReciprocalAlgebra
    referenceAlgebra positiveAlgebra
rationalPositiveMassReciprocalAlgebra interpretation = record
  { reciprocal = safeRationalReciprocal
  ; reciprocalTimesPositive = λ value positive →
      trans
        (multiplyMeaning interpretation (safeRationalReciprocal value) value)
        (trans
          (safeRationalReciprocalTimesPositive value
            (positiveMeansRationalPositive interpretation positive))
          (sym (oneMeaning interpretation)))
  }

safeRationalReciprocalDefinitionLevel : ProofLevel
safeRationalReciprocalDefinitionLevel = machineChecked

positiveRationalReciprocalLawLevel : ProofLevel
positiveRationalReciprocalLawLevel = machineChecked

rationalReferenceReciprocalInstanceLevel : ProofLevel
rationalReferenceReciprocalInstanceLevel = machineChecked

physicalReferencePositiveMeansRationalPositiveInputsLevel : ProofLevel
physicalReferencePositiveMeansRationalPositiveInputsLevel = conditional

physicalReferenceRationalAlgebraMeaningInputsLevel : ProofLevel
physicalReferenceRationalAlgebraMeaningInputsLevel = conditional
