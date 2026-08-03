module DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibrePositiveMassExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayP3FiniteConstrainedIntegralExact as Integral
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibreNormalizationExact as Reference

------------------------------------------------------------------------
-- Primary provenance.
--
-- André Weil, "L'intégration dans les groupes topologiques et ses
-- applications", Hermann, Paris (1940). No DOI assigned.
--
-- Gerald B. Folland, "A Course in Abstract Harmonic Analysis", second
-- edition, CRC Press (2016). DOI: 10.1201/b19172.
--
-- The theorem below is the finite constrained analogue actually used by the
-- repository: a nonempty selected fibre with nonnegative weights and one
-- strictly positive weight has strictly positive total mass.  No continuum
-- Haar-positivity theorem is imported as a substitute for that finite fact.
------------------------------------------------------------------------

data Empty : Set where

infix 4 _∈_
data _∈_ {A : Set} (value : A) : List A → Set where
  here : ∀ {values} → value ∈ (value ∷ values)
  there : ∀ {head values} → value ∈ values → value ∈ (head ∷ values)

record PositiveFiniteFoldAlgebra
    {Fine SlowField Scalar : Set}
    (sumData : Integral.FiniteConstrainedSum Fine SlowField Scalar) : Set₁ where
  field
    Nonnegative Positive : Scalar → Set

    zeroNonnegative : Nonnegative (Integral.zero sumData)
    addNonnegative : ∀ {left right} →
      Nonnegative left → Nonnegative right →
      Nonnegative (Integral.add sumData left right)
    addPositiveLeft : ∀ {left right} →
      Positive left → Nonnegative right →
      Positive (Integral.add sumData left right)
    addPositiveRight : ∀ {left right} →
      Nonnegative left → Positive right →
      Positive (Integral.add sumData left right)

    positiveImpliesNonzero : ∀ {value} →
      Positive value → value ≡ Integral.zero sumData → Empty

open PositiveFiniteFoldAlgebra public

foldNonnegative :
  ∀ {Fine SlowField Scalar}
    {sumData : Integral.FiniteConstrainedSum Fine SlowField Scalar}
    (algebra : PositiveFiniteFoldAlgebra sumData)
    selector slow fields →
  (∀ (fld : Fine) → Nonnegative algebra (selector fld)) →
  Nonnegative algebra
    (Integral.foldSelected sumData selector slow fields)
foldNonnegative algebra selector slow [] pointwise =
  zeroNonnegative algebra
foldNonnegative {sumData = sumData} algebra selector slow
  (fld ∷ fields) pointwise =
  addNonnegative algebra
    (pointwise fld)
    (foldNonnegative algebra selector slow fields pointwise)

foldPositiveAtMember :
  ∀ {Fine SlowField Scalar}
    {sumData : Integral.FiniteConstrainedSum Fine SlowField Scalar}
    (algebra : PositiveFiniteFoldAlgebra sumData)
    selector slow fields witness →
  witness ∈ fields →
  (∀ (fld : Fine) → Nonnegative algebra (selector fld)) →
  Positive algebra (selector witness) →
  Positive algebra
    (Integral.foldSelected sumData selector slow fields)
foldPositiveAtMember algebra selector slow [] witness () pointwise positive
foldPositiveAtMember {sumData = sumData} algebra selector slow
  (.witness ∷ fields) witness here pointwise positive =
  addPositiveLeft algebra positive
    (foldNonnegative algebra selector slow fields pointwise)
foldPositiveAtMember {sumData = sumData} algebra selector slow
  (fld ∷ fields) witness (there membership) pointwise positive =
  addPositiveRight algebra
    (pointwise fld)
    (foldPositiveAtMember algebra selector slow fields witness
      membership pointwise positive)

record PositiveSelectedReferenceFibre
    {Fine SlowField Scalar : Set}
    {sumData : Integral.FiniteConstrainedSum Fine SlowField Scalar}
    (algebra : PositiveFiniteFoldAlgebra sumData)
    (selector : Fine → Scalar)
    (slow : SlowField)
    (fields : List Fine) : Set₁ where
  field
    selectedWeightNonnegative : ∀ (fld : Fine) →
      Nonnegative algebra (selector fld)

    witness : Fine
    witnessInFibre : witness ∈ fields
    witnessWeightPositive : Positive algebra (selector witness)

open PositiveSelectedReferenceFibre public

selectedReferenceMassPositive :
  ∀ {Fine SlowField Scalar}
    {sumData : Integral.FiniteConstrainedSum Fine SlowField Scalar}
    {algebra : PositiveFiniteFoldAlgebra sumData}
    {selector : Fine → Scalar} {slow fields} →
  PositiveSelectedReferenceFibre algebra selector slow fields →
  Positive algebra
    (Integral.foldSelected sumData selector slow fields)
selectedReferenceMassPositive {algebra = algebra} {selector = selector}
  {slow = slow} {fields = fields} dataSet =
  foldPositiveAtMember algebra selector slow fields
    (witness dataSet)
    (witnessInFibre dataSet)
    (selectedWeightNonnegative dataSet)
    (witnessWeightPositive dataSet)

selectedReferenceMassNonzero :
  ∀ {Fine SlowField Scalar}
    {sumData : Integral.FiniteConstrainedSum Fine SlowField Scalar}
    {algebra : PositiveFiniteFoldAlgebra sumData}
    {selector : Fine → Scalar} {slow fields} →
  PositiveSelectedReferenceFibre algebra selector slow fields →
  Integral.foldSelected sumData selector slow fields
    ≡ Integral.zero sumData → Empty
selectedReferenceMassNonzero {algebra = algebra} dataSet =
  positiveImpliesNonzero algebra (selectedReferenceMassPositive dataSet)

record PositiveMassReciprocalAlgebra
    {Fine SlowField Scalar : Set}
    {sumData : Integral.FiniteConstrainedSum Fine SlowField Scalar}
    (referenceAlgebra : Reference.FiniteReferenceFibreAlgebra sumData)
    (positiveAlgebra : PositiveFiniteFoldAlgebra sumData) : Set₁ where
  field
    reciprocal : Scalar → Scalar
    reciprocalTimesPositive : ∀ (value : Scalar) →
      Positive positiveAlgebra value →
      Reference.multiply referenceAlgebra (reciprocal value) value
      ≡ Reference.one referenceAlgebra

open PositiveMassReciprocalAlgebra public

reciprocalReferenceMassFromPositiveWitness :
  ∀ {Fine SlowField Scalar}
    {sumData : Integral.FiniteConstrainedSum Fine SlowField Scalar}
    {referenceAlgebra : Reference.FiniteReferenceFibreAlgebra sumData}
    {positiveAlgebra : PositiveFiniteFoldAlgebra sumData}
    (reciprocalAlgebra : PositiveMassReciprocalAlgebra
      referenceAlgebra positiveAlgebra)
    {selector : Fine → Scalar} {slow fields} →
  PositiveSelectedReferenceFibre positiveAlgebra selector slow fields →
  Reference.ReciprocalReferenceMass
    referenceAlgebra selector slow fields
reciprocalReferenceMassFromPositiveWitness
  {sumData = sumData} {referenceAlgebra = referenceAlgebra}
  {positiveAlgebra = positiveAlgebra}
  reciprocalAlgebra {selector = selector} {slow = slow} {fields = fields}
  positiveFibre = record
  { mass = Integral.foldSelected sumData selector slow fields
  ; reciprocalMass = reciprocal reciprocalAlgebra
      (Integral.foldSelected sumData selector slow fields)
  ; massDefinition = refl
  ; reciprocalTimesMass = reciprocalTimesPositive reciprocalAlgebra
      (Integral.foldSelected sumData selector slow fields)
      (selectedReferenceMassPositive positiveFibre)
  }

finiteReferenceMassNonnegativeFoldLevel : ProofLevel
finiteReferenceMassNonnegativeFoldLevel = machineChecked

finiteReferenceMassPositiveWitnessLevel : ProofLevel
finiteReferenceMassPositiveWitnessLevel = machineChecked

finiteReferenceMassNonzeroLevel : ProofLevel
finiteReferenceMassNonzeroLevel = machineChecked

positiveMassReciprocalConstructionLevel : ProofLevel
positiveMassReciprocalConstructionLevel = machineChecked

physicalReferenceFibrePositiveWitnessInputsLevel : ProofLevel
physicalReferenceFibrePositiveWitnessInputsLevel = conditional

physicalPositiveMassReciprocalInputsLevel : ProofLevel
physicalPositiveMassReciprocalInputsLevel = conditional
