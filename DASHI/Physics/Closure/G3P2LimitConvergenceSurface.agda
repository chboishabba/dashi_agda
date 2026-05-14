module DASHI.Physics.Closure.G3P2LimitConvergenceSurface where

open import Agda.Primitive using (Set; Setω; lzero; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _==_)
open import Agda.Builtin.String using (String)
open import Data.Integer as ℤ using (∣_∣)
open import Data.List.Base using (List; _∷_; []; _++_)
open import Data.Nat.Base using (_∸_; _≤_; z≤n; s≤s)
open import Data.Rational as Rat using (↥_; ↧ₙ_)
import Data.Rational.Properties as RatProps
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import DASHI.Core.Q using (ℚ; 0ℚ; 1ℚ)
import DASHI.Arithmetic.ArithmeticIntegerEmbedding as AIE
import Ultrametric as UMetric
import DASHI.Geometry.CompleteUltrametric as CompleteU
import DASHI.Geometry.CompleteUltrametricNat as CompleteUNat
import DASHI.Physics.Closure.G3ConcreteOperators as G3Concrete
import DASHI.Physics.Closure.G3P2AdicNormMetricSurface as G3Norm
import DASHI.Physics.Closure.G3WaveFunctionOperatorAlgebra as G3Wave
import Ontology.GodelLattice as GL

------------------------------------------------------------------------
-- Selected p2 limit-convergence surface.
--
-- The repo already contains the only general convergence theorem this lane
-- can honestly consume without adding analytic real-number machinery:
-- every Nat-valued ultrametric is complete.  This surface connects that
-- theorem to the selected G3 wave-function operator carrier and narrows the
-- former "missingP2LimitConvergencePrimitive" into the concrete missing
-- pieces needed by the contraction lane:
--
--   1. a selected p2 operator ultrametric whose Nat distance is tied to the
--      existing p2 norm-index evidence;
--   2. a rescaled-boost sequence in that ultrametric;
--   3. a Cauchy/convergence witness for that sequence.
--
-- No Schrodinger/Poincare-to-Galilei contraction carrier is promoted here.

data G3P2LimitConvergenceStatus : Set where
  selectedP2LimitReducedToNatUltrametricCompletenessNoPromotion :
    G3P2LimitConvergenceStatus

data G3P2LimitConvergenceMissingPrimitive : Set where
  missingSelectedP2OperatorDistancePrimitive :
    G3P2LimitConvergenceMissingPrimitive

  missingSelectedOperatorNormIndexFunction :
    G3P2LimitConvergenceMissingPrimitive

  missingSelectedOperatorDifferenceNormIndex :
    G3P2LimitConvergenceMissingPrimitive

  missingSelectedOperatorNormIdentityZero :
    G3P2LimitConvergenceMissingPrimitive

  missingSelectedOperatorDifferenceNormSymmetry :
    G3P2LimitConvergenceMissingPrimitive

  missingSelectedOperatorDifferenceNormUltrametric :
    G3P2LimitConvergenceMissingPrimitive

  missingSelectedP2OperatorUltrametric :
    G3P2LimitConvergenceMissingPrimitive

  missingSelectedP2OperatorRescalingPrimitive :
    G3P2LimitConvergenceMissingPrimitive

  missingSelectedOperatorRescalingDistanceBound :
    G3P2LimitConvergenceMissingPrimitive

  missingSelectedP2RescaledBoostSequence :
    G3P2LimitConvergenceMissingPrimitive

  missingSelectedP2RescaledBoostCauchyWitness :
    G3P2LimitConvergenceMissingPrimitive

  missingSelectedP2RescaledBoostZeroLimitWitness :
    G3P2LimitConvergenceMissingPrimitive

data G3P2OperatorNormIndexMissingLaw : Set where
  missingSelectedWaveFunctionBasisCarrier :
    G3P2OperatorNormIndexMissingLaw

  missingSelectedWaveFunctionBasisVector :
    G3P2OperatorNormIndexMissingLaw

  missingSelectedWaveFunctionBasisCoefficient :
    G3P2OperatorNormIndexMissingLaw

  missingSelectedOperatorMatrixElement :
    G3P2OperatorNormIndexMissingLaw

  missingMatrixElementP2Valuation :
    G3P2OperatorNormIndexMissingLaw

  missingFiniteSupportMinimumForNonzeroMatrixElements :
    G3P2OperatorNormIndexMissingLaw

  missingGlobalFiniteNonzeroMatrixSupportWitness :
    G3P2OperatorNormIndexMissingLaw

  missingSelectedOperatorNormIndexMinimumLaw :
    G3P2OperatorNormIndexMissingLaw

  missingSelectedOperatorNormIndexDegreeSoundness :
    G3P2OperatorNormIndexMissingLaw

  missingSelectedOperatorDifferenceNormIndexLaws :
    G3P2OperatorNormIndexMissingLaw

SelectedOperator :
  Set
SelectedOperator =
  G3Wave.WaveFunctionOperator

SelectedWaveFunctionBasisCarrier :
  Set
SelectedWaveFunctionBasisCarrier =
  G3Wave.SelectedG3State

_&&_ :
  Bool →
  Bool →
  Bool
infixr 6 _&&_
true && y =
  y
false && y =
  false

selectedG3StateCoordinateEquality :
  G3Wave.SelectedG3State →
  G3Wave.SelectedG3State →
  Bool
selectedG3StateCoordinateEquality
  (GL.v15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71)
  (GL.v15 b2 b3 b5 b7 b11 b13 b17 b19 b23 b29 b31 b41 b47 b59 b71) =
  (a2 == b2)
  && (a3 == b3)
  && (a5 == b5)
  && (a7 == b7)
  && (a11 == b11)
  && (a13 == b13)
  && (a17 == b17)
  && (a19 == b19)
  && (a23 == b23)
  && (a29 == b29)
  && (a31 == b31)
  && (a41 == b41)
  && (a47 == b47)
  && (a59 == b59)
  && (a71 == b71)

selectedWaveFunctionBasisVector :
  G3Wave.SelectedG3State →
  G3Wave.WaveFunction
selectedWaveFunctionBasisVector source target
  with selectedG3StateCoordinateEquality source target
... | true =
  1ℚ
... | false =
  0ℚ

selectedWaveFunctionBasisCoefficient :
  G3Wave.WaveFunction →
  G3Wave.SelectedG3State →
  ℚ
selectedWaveFunctionBasisCoefficient ψ basis =
  ψ basis

selectedOperatorMatrixElement :
  G3Wave.WaveFunctionOperator →
  G3Wave.SelectedG3State →
  G3Wave.SelectedG3State →
  ℚ
selectedOperatorMatrixElement A source target =
  selectedWaveFunctionBasisCoefficient
    (A (selectedWaveFunctionBasisVector source))
    target

matrixElementP2Valuation :
  ℚ →
  Nat
matrixElementP2Valuation q =
  AIE.vp 2 (∣ ↥ q ∣)
  ∸
  AIE.vp 2 (↧ₙ q)

¬_ :
  Set →
  Set
¬ P =
  P → ⊥

minNat :
  Nat →
  Nat →
  Nat
minNat zero _ =
  zero
minNat (suc _) zero =
  zero
minNat (suc m) (suc n) =
  suc (minNat m n)

≤-trans :
  {a b c : Nat} →
  a ≤ b →
  b ≤ c →
  a ≤ c
≤-trans z≤n _ =
  z≤n
≤-trans (s≤s a≤b) (s≤s b≤c) =
  s≤s (≤-trans a≤b b≤c)

minNat-left-lower :
  (m n : Nat) →
  minNat m n ≤ m
minNat-left-lower zero _ =
  z≤n
minNat-left-lower (suc _) zero =
  z≤n
minNat-left-lower (suc m) (suc n) =
  s≤s (minNat-left-lower m n)

minNat-right-lower :
  (m n : Nat) →
  minNat m n ≤ n
minNat-right-lower zero _ =
  z≤n
minNat-right-lower (suc _) zero =
  z≤n
minNat-right-lower (suc m) (suc n) =
  s≤s (minNat-right-lower m n)

≤-minNat :
  {k m n : Nat} →
  k ≤ m →
  k ≤ n →
  k ≤ minNat m n
≤-minNat {zero} _ _ =
  z≤n
≤-minNat {suc _} {zero} ()
≤-minNat {suc _} {suc _} {zero} _ ()
≤-minNat {suc k} {suc m} {suc n} (s≤s k≤m) (s≤s k≤n) =
  s≤s (≤-minNat {k} {m} {n} k≤m k≤n)

record G3SelectedMatrixIndexPair : Set where
  constructor _,ᵐ_
  field
    source :
      G3Wave.SelectedG3State

    target :
      G3Wave.SelectedG3State

open G3SelectedMatrixIndexPair

data MatrixIndexPairListed :
  G3SelectedMatrixIndexPair →
  List G3SelectedMatrixIndexPair →
  Set where
  here :
    {p : G3SelectedMatrixIndexPair} →
    {rest : List G3SelectedMatrixIndexPair} →
    MatrixIndexPairListed p (p ∷ rest)

  there :
    {p q : G3SelectedMatrixIndexPair} →
    {rest : List G3SelectedMatrixIndexPair} →
    MatrixIndexPairListed p rest →
    MatrixIndexPairListed p (q ∷ rest)

matrixIndexPairListed-++ˡ :
  {entry : G3SelectedMatrixIndexPair} →
  (left right : List G3SelectedMatrixIndexPair) →
  MatrixIndexPairListed entry left →
  MatrixIndexPairListed entry (left ++ right)
matrixIndexPairListed-++ˡ [] right ()
matrixIndexPairListed-++ˡ (head ∷ rest) right here =
  here
matrixIndexPairListed-++ˡ (head ∷ rest) right (there listed) =
  there (matrixIndexPairListed-++ˡ rest right listed)

matrixIndexPairListed-++ʳ :
  {entry : G3SelectedMatrixIndexPair} →
  (left right : List G3SelectedMatrixIndexPair) →
  MatrixIndexPairListed entry right →
  MatrixIndexPairListed entry (left ++ right)
matrixIndexPairListed-++ʳ [] right listed =
  listed
matrixIndexPairListed-++ʳ (head ∷ rest) right listed =
  there (matrixIndexPairListed-++ʳ rest right listed)

record G3FiniteNonzeroMatrixSupportWitness
  (A : G3Wave.WaveFunctionOperator) : Set where
  field
    support :
      List G3SelectedMatrixIndexPair

    emptySupportSentinel :
      Nat

    supportEntriesAreNonzero :
      (entry : G3SelectedMatrixIndexPair) →
      MatrixIndexPairListed entry support →
      ¬
      (
        selectedOperatorMatrixElement
          A
          (source entry)
          (target entry)
        ≡
        0ℚ
      )

    supportCoversEveryNonzeroMatrixElement :
      (source target : G3Wave.SelectedG3State) →
      ¬ (selectedOperatorMatrixElement A source target ≡ 0ℚ) →
      MatrixIndexPairListed (source ,ᵐ target) support

finiteSupportMinimumForNonzeroMatrixElementsFromList :
  G3Wave.WaveFunctionOperator →
  Nat →
  List G3SelectedMatrixIndexPair →
  Nat
finiteSupportMinimumForNonzeroMatrixElementsFromList A sentinel [] =
  sentinel
finiteSupportMinimumForNonzeroMatrixElementsFromList A sentinel (entry ∷ rest) =
  minNat
    (matrixElementP2Valuation
      (selectedOperatorMatrixElement A (source entry) (target entry)))
    (finiteSupportMinimumForNonzeroMatrixElementsFromList A sentinel rest)

finiteSupportMinimumForNonzeroMatrixElements :
  (A : G3Wave.WaveFunctionOperator) →
  G3FiniteNonzeroMatrixSupportWitness A →
  Nat
finiteSupportMinimumForNonzeroMatrixElements A witness =
  finiteSupportMinimumForNonzeroMatrixElementsFromList
    A
    (G3FiniteNonzeroMatrixSupportWitness.emptySupportSentinel witness)
    (G3FiniteNonzeroMatrixSupportWitness.support witness)

SelectedOperatorP2Degree :
  G3Wave.WaveFunctionOperator →
  Nat →
  Set
SelectedOperatorP2Degree A n =
  (src tgt : G3Wave.SelectedG3State) →
  ¬ (selectedOperatorMatrixElement A src tgt ≡ 0ℚ) →
  n
  ≤
  matrixElementP2Valuation (selectedOperatorMatrixElement A src tgt)

SupportValuationsBoundedBelow :
  G3Wave.WaveFunctionOperator →
  List G3SelectedMatrixIndexPair →
  Nat →
  Set
SupportValuationsBoundedBelow A support n =
  (entry : G3SelectedMatrixIndexPair) →
  MatrixIndexPairListed entry support →
  n
  ≤
  matrixElementP2Valuation
    (selectedOperatorMatrixElement A (source entry) (target entry))

finiteSupportMinimumForNonzeroMatrixElementsFromListBelowListed :
  (A : G3Wave.WaveFunctionOperator) →
  (sentinel : Nat) →
  (entry : G3SelectedMatrixIndexPair) →
  (support : List G3SelectedMatrixIndexPair) →
  MatrixIndexPairListed entry support →
  finiteSupportMinimumForNonzeroMatrixElementsFromList A sentinel support
  ≤
  matrixElementP2Valuation
    (selectedOperatorMatrixElement A (source entry) (target entry))
finiteSupportMinimumForNonzeroMatrixElementsFromListBelowListed
  A sentinel entry [] ()
finiteSupportMinimumForNonzeroMatrixElementsFromListBelowListed
  A sentinel entry (entry ∷ rest) here =
  minNat-left-lower
    (matrixElementP2Valuation
      (selectedOperatorMatrixElement A (source entry) (target entry)))
    (finiteSupportMinimumForNonzeroMatrixElementsFromList A sentinel rest)
finiteSupportMinimumForNonzeroMatrixElementsFromListBelowListed
  A sentinel entry (head ∷ rest) (there listed) =
  ≤-trans
    (minNat-right-lower
      (matrixElementP2Valuation
        (selectedOperatorMatrixElement A (source head) (target head)))
      (finiteSupportMinimumForNonzeroMatrixElementsFromList A sentinel rest))
    (finiteSupportMinimumForNonzeroMatrixElementsFromListBelowListed
      A sentinel entry rest listed)

finiteSupportMinimumBoundImpliesSupportValuationsBoundedBelow :
  (A : G3Wave.WaveFunctionOperator) →
  (sentinel n : Nat) →
  (support : List G3SelectedMatrixIndexPair) →
  n ≤ finiteSupportMinimumForNonzeroMatrixElementsFromList A sentinel support →
  SupportValuationsBoundedBelow A support n
finiteSupportMinimumBoundImpliesSupportValuationsBoundedBelow
  A sentinel n [] minBound entry ()
finiteSupportMinimumBoundImpliesSupportValuationsBoundedBelow
  A sentinel n (entry ∷ rest) minBound entry here =
  ≤-trans
    minBound
    (minNat-left-lower
      (matrixElementP2Valuation
        (selectedOperatorMatrixElement A (source entry) (target entry)))
      (finiteSupportMinimumForNonzeroMatrixElementsFromList A sentinel rest))
finiteSupportMinimumBoundImpliesSupportValuationsBoundedBelow
  A sentinel n (head ∷ rest) minBound entry (there listed) =
  finiteSupportMinimumBoundImpliesSupportValuationsBoundedBelow
    A
    sentinel
    n
    rest
    (≤-trans
      minBound
      (minNat-right-lower
        (matrixElementP2Valuation
          (selectedOperatorMatrixElement A (source head) (target head)))
        (finiteSupportMinimumForNonzeroMatrixElementsFromList A sentinel rest)))
    entry
    listed

supportValuationsAndSentinelBoundedBelowImpliesFiniteSupportMinimumBound :
  (A : G3Wave.WaveFunctionOperator) →
  (sentinel n : Nat) →
  (support : List G3SelectedMatrixIndexPair) →
  n ≤ sentinel →
  SupportValuationsBoundedBelow A support n →
  n ≤ finiteSupportMinimumForNonzeroMatrixElementsFromList A sentinel support
supportValuationsAndSentinelBoundedBelowImpliesFiniteSupportMinimumBound
  A sentinel n [] sentinelBound supportBound =
  sentinelBound
supportValuationsAndSentinelBoundedBelowImpliesFiniteSupportMinimumBound
  A sentinel n (entry ∷ rest) sentinelBound supportBound =
  ≤-minNat
    (supportBound entry here)
    (supportValuationsAndSentinelBoundedBelowImpliesFiniteSupportMinimumBound
      A
      sentinel
      n
      rest
      sentinelBound
      (λ restEntry listed → supportBound restEntry (there listed)))

record G3ConstructiveFiniteSupportOperator : Set where
  constructor finiteSupportOperator
  field
    operator :
      G3Wave.WaveFunctionOperator

    finiteSupportWitness :
      G3FiniteNonzeroMatrixSupportWitness operator

open G3ConstructiveFiniteSupportOperator

selectedFiniteSupportOperatorNormIndex :
  G3ConstructiveFiniteSupportOperator →
  Nat
selectedFiniteSupportOperatorNormIndex A# =
  finiteSupportMinimumForNonzeroMatrixElements
    (operator A#)
    (finiteSupportWitness A#)

selectedFiniteSupportOperatorNormIndexMinimumLaw :
  (A# : G3ConstructiveFiniteSupportOperator) →
  selectedFiniteSupportOperatorNormIndex A#
  ≡
  finiteSupportMinimumForNonzeroMatrixElements
    (operator A#)
    (finiteSupportWitness A#)
selectedFiniteSupportOperatorNormIndexMinimumLaw _ =
  refl

selectedFiniteSupportOperatorNormIndexDegreeSoundness :
  (A# : G3ConstructiveFiniteSupportOperator) →
  SelectedOperatorP2Degree
    (operator A#)
    (selectedFiniteSupportOperatorNormIndex A#)
selectedFiniteSupportOperatorNormIndexDegreeSoundness A# src tgt nonzero =
  let
    witness =
      finiteSupportWitness A#
  in
  finiteSupportMinimumForNonzeroMatrixElementsFromListBelowListed
    (operator A#)
    (G3FiniteNonzeroMatrixSupportWitness.emptySupportSentinel witness)
    (src ,ᵐ tgt)
    (G3FiniteNonzeroMatrixSupportWitness.support witness)
    (G3FiniteNonzeroMatrixSupportWitness.supportCoversEveryNonzeroMatrixElement
      witness
      src
      tgt
      nonzero)

selectedOperatorSubtractionZeroIfBothZero :
  (A B : G3Wave.WaveFunctionOperator) →
  (src tgt : G3Wave.SelectedG3State) →
  selectedOperatorMatrixElement A src tgt ≡ 0ℚ →
  selectedOperatorMatrixElement B src tgt ≡ 0ℚ →
  selectedOperatorMatrixElement
    (G3Wave.waveFunctionOperatorSubtraction A B)
    src
    tgt
  ≡
  0ℚ
selectedOperatorSubtractionZeroIfBothZero A B src tgt aZero bZero
  rewrite aZero | bZero =
  refl

selectedOperatorSubtractionNonzeroImpliesOperandNonzero :
  (A B : G3Wave.WaveFunctionOperator) →
  (src tgt : G3Wave.SelectedG3State) →
  ¬
  (
    selectedOperatorMatrixElement
      (G3Wave.waveFunctionOperatorSubtraction A B)
      src
      tgt
    ≡
    0ℚ
  ) →
  ¬ (selectedOperatorMatrixElement A src tgt ≡ 0ℚ)
  ⊎
  ¬ (selectedOperatorMatrixElement B src tgt ≡ 0ℚ)
selectedOperatorSubtractionNonzeroImpliesOperandNonzero
  A B src tgt subtractionNonzero
  with RatProps._≟_ (selectedOperatorMatrixElement A src tgt) 0ℚ
... | no aNonzero =
  inj₁ aNonzero
... | yes aZero =
  inj₂
    (λ bZero →
      subtractionNonzero
        (selectedOperatorSubtractionZeroIfBothZero
          A
          B
          src
          tgt
          aZero
          bZero))

selectedFiniteSupportOperatorSubtractionSupportCandidate :
  (A# B# : G3ConstructiveFiniteSupportOperator) →
  List G3SelectedMatrixIndexPair
selectedFiniteSupportOperatorSubtractionSupportCandidate A# B# =
  G3FiniteNonzeroMatrixSupportWitness.support (finiteSupportWitness A#)
  ++
  G3FiniteNonzeroMatrixSupportWitness.support (finiteSupportWitness B#)

SelectedSubtractionCandidateEntriesAreNonzero :
  (A# B# : G3ConstructiveFiniteSupportOperator) →
  Set
SelectedSubtractionCandidateEntriesAreNonzero A# B# =
  (entry : G3SelectedMatrixIndexPair) →
  MatrixIndexPairListed
    entry
    (selectedFiniteSupportOperatorSubtractionSupportCandidate A# B#) →
  ¬
  (
    selectedOperatorMatrixElement
      (G3Wave.waveFunctionOperatorSubtraction (operator A#) (operator B#))
      (source entry)
      (target entry)
    ≡
    0ℚ
  )

selectedFiniteSupportOperatorSubtractionCandidateCoversEveryNonzero :
  (A# B# : G3ConstructiveFiniteSupportOperator) →
  (src tgt : G3Wave.SelectedG3State) →
  ¬
  (
    selectedOperatorMatrixElement
      (G3Wave.waveFunctionOperatorSubtraction (operator A#) (operator B#))
      src
      tgt
    ≡
    0ℚ
  ) →
  MatrixIndexPairListed
    (src ,ᵐ tgt)
    (selectedFiniteSupportOperatorSubtractionSupportCandidate A# B#)
selectedFiniteSupportOperatorSubtractionCandidateCoversEveryNonzero
  A# B# src tgt subtractionNonzero
  with selectedOperatorSubtractionNonzeroImpliesOperandNonzero
    (operator A#)
    (operator B#)
    src
    tgt
    subtractionNonzero
... | inj₁ aNonzero =
  matrixIndexPairListed-++ˡ
    (G3FiniteNonzeroMatrixSupportWitness.support (finiteSupportWitness A#))
    (G3FiniteNonzeroMatrixSupportWitness.support (finiteSupportWitness B#))
    (G3FiniteNonzeroMatrixSupportWitness.supportCoversEveryNonzeroMatrixElement
      (finiteSupportWitness A#)
      src
      tgt
      aNonzero)
... | inj₂ bNonzero =
  matrixIndexPairListed-++ʳ
    (G3FiniteNonzeroMatrixSupportWitness.support (finiteSupportWitness A#))
    (G3FiniteNonzeroMatrixSupportWitness.support (finiteSupportWitness B#))
    (G3FiniteNonzeroMatrixSupportWitness.supportCoversEveryNonzeroMatrixElement
      (finiteSupportWitness B#)
      src
      tgt
      bNonzero)

selectedFiniteSupportOperatorSubtractionSupportWitnessFromCandidate :
  (A# B# : G3ConstructiveFiniteSupportOperator) →
  Nat →
  SelectedSubtractionCandidateEntriesAreNonzero A# B# →
  G3FiniteNonzeroMatrixSupportWitness
    (G3Wave.waveFunctionOperatorSubtraction (operator A#) (operator B#))
selectedFiniteSupportOperatorSubtractionSupportWitnessFromCandidate
  A# B# sentinel candidateEntriesAreNonzero =
  record
    { support =
        selectedFiniteSupportOperatorSubtractionSupportCandidate A# B#
    ; emptySupportSentinel =
        sentinel
    ; supportEntriesAreNonzero =
        candidateEntriesAreNonzero
    ; supportCoversEveryNonzeroMatrixElement =
        selectedFiniteSupportOperatorSubtractionCandidateCoversEveryNonzero
          A#
          B#
    }

G3FiniteSupportOperatorFiltrationDegree :
  G3ConstructiveFiniteSupportOperator →
  Nat →
  Set
G3FiniteSupportOperatorFiltrationDegree A# n =
  SelectedOperatorP2Degree (operator A#) n

selectedFiniteSupportOperatorDifference :
  (A# B# : G3ConstructiveFiniteSupportOperator) →
  G3FiniteNonzeroMatrixSupportWitness
    (G3Wave.waveFunctionOperatorSubtraction (operator A#) (operator B#)) →
  G3ConstructiveFiniteSupportOperator
selectedFiniteSupportOperatorDifference A# B# witness =
  finiteSupportOperator
    (G3Wave.waveFunctionOperatorSubtraction (operator A#) (operator B#))
    witness

selectedFiniteSupportOperatorDifferenceForgetsToSubtraction :
  (A# B# : G3ConstructiveFiniteSupportOperator) →
  (witness :
    G3FiniteNonzeroMatrixSupportWitness
      (G3Wave.waveFunctionOperatorSubtraction (operator A#) (operator B#))) →
  operator (selectedFiniteSupportOperatorDifference A# B# witness)
  ≡
  G3Wave.waveFunctionOperatorSubtraction (operator A#) (operator B#)
selectedFiniteSupportOperatorDifferenceForgetsToSubtraction _ _ _ =
  refl

selectedFiniteSupportOperatorDifferenceNormIndex :
  (A# B# : G3ConstructiveFiniteSupportOperator) →
  G3FiniteNonzeroMatrixSupportWitness
    (G3Wave.waveFunctionOperatorSubtraction (operator A#) (operator B#)) →
  Nat
selectedFiniteSupportOperatorDifferenceNormIndex A# B# witness =
  selectedFiniteSupportOperatorNormIndex
    (selectedFiniteSupportOperatorDifference A# B# witness)

selectedFiniteSupportOperatorDifferenceNormIndexMinimumLaw :
  (A# B# : G3ConstructiveFiniteSupportOperator) →
  (witness :
    G3FiniteNonzeroMatrixSupportWitness
      (G3Wave.waveFunctionOperatorSubtraction (operator A#) (operator B#))) →
  selectedFiniteSupportOperatorDifferenceNormIndex A# B# witness
  ≡
  finiteSupportMinimumForNonzeroMatrixElements
    (G3Wave.waveFunctionOperatorSubtraction (operator A#) (operator B#))
    witness
selectedFiniteSupportOperatorDifferenceNormIndexMinimumLaw _ _ _ =
  refl

selectedFiniteSupportOperatorDifferenceNormIndexDegreeSoundness :
  (A# B# : G3ConstructiveFiniteSupportOperator) →
  (witness :
    G3FiniteNonzeroMatrixSupportWitness
      (G3Wave.waveFunctionOperatorSubtraction (operator A#) (operator B#))) →
  SelectedOperatorP2Degree
    (G3Wave.waveFunctionOperatorSubtraction (operator A#) (operator B#))
    (selectedFiniteSupportOperatorDifferenceNormIndex A# B# witness)
selectedFiniteSupportOperatorDifferenceNormIndexDegreeSoundness A# B# witness =
  selectedFiniteSupportOperatorNormIndexDegreeSoundness
    (selectedFiniteSupportOperatorDifference A# B# witness)

selectedWaveFunctionOperatorSubtractionSymmetryPointwise :
  (A B : G3Wave.WaveFunctionOperator) →
  G3Wave.WaveFunctionOperatorPointwiseEquality
    (G3Wave.waveFunctionOperatorSubtraction B A)
    (G3Wave.waveFunctionOperatorNegation
      (G3Wave.waveFunctionOperatorSubtraction A B))
selectedWaveFunctionOperatorSubtractionSymmetryPointwise =
  G3Wave.waveFunctionOperatorNegatedDifferencePointwise

record G3FiniteSupportDifferenceNormLawSurface : Setω where
  field
    finiteSupportOperatorSubtype :
      Set

    finiteSupportOperatorSubtypeIsConstructive :
      finiteSupportOperatorSubtype ≡ G3ConstructiveFiniteSupportOperator

    selectedDifferenceOperatorPrimitive :
      (A# B# : G3ConstructiveFiniteSupportOperator) →
      G3FiniteNonzeroMatrixSupportWitness
        (G3Wave.waveFunctionOperatorSubtraction (operator A#) (operator B#)) →
      G3ConstructiveFiniteSupportOperator

    selectedDifferenceOperatorForgetsToSubtraction :
      (A# B# : G3ConstructiveFiniteSupportOperator) →
      (witness :
        G3FiniteNonzeroMatrixSupportWitness
          (G3Wave.waveFunctionOperatorSubtraction
            (operator A#)
            (operator B#))) →
      operator (selectedDifferenceOperatorPrimitive A# B# witness)
      ≡
      G3Wave.waveFunctionOperatorSubtraction (operator A#) (operator B#)

    selectedDifferenceNormIndexPrimitive :
      (A# B# : G3ConstructiveFiniteSupportOperator) →
      G3FiniteNonzeroMatrixSupportWitness
        (G3Wave.waveFunctionOperatorSubtraction (operator A#) (operator B#)) →
      Nat

    selectedDifferenceNormIndexMinimumLaw :
      (A# B# : G3ConstructiveFiniteSupportOperator) →
      (witness :
        G3FiniteNonzeroMatrixSupportWitness
          (G3Wave.waveFunctionOperatorSubtraction
            (operator A#)
            (operator B#))) →
      selectedDifferenceNormIndexPrimitive A# B# witness
      ≡
      finiteSupportMinimumForNonzeroMatrixElements
        (G3Wave.waveFunctionOperatorSubtraction (operator A#) (operator B#))
        witness

    selectedDifferenceNormIndexDegreeSoundness :
      (A# B# : G3ConstructiveFiniteSupportOperator) →
      (witness :
        G3FiniteNonzeroMatrixSupportWitness
          (G3Wave.waveFunctionOperatorSubtraction
            (operator A#)
            (operator B#))) →
      SelectedOperatorP2Degree
        (G3Wave.waveFunctionOperatorSubtraction (operator A#) (operator B#))
        (selectedDifferenceNormIndexPrimitive A# B# witness)

    subtractionSymmetryPointwise :
      (A B : G3Wave.WaveFunctionOperator) →
      G3Wave.WaveFunctionOperatorPointwiseEquality
        (G3Wave.waveFunctionOperatorSubtraction B A)
        (G3Wave.waveFunctionOperatorNegation
          (G3Wave.waveFunctionOperatorSubtraction A B))

    selectedSubtractionSupportCandidate :
      (A# B# : G3ConstructiveFiniteSupportOperator) →
      List G3SelectedMatrixIndexPair

    selectedSubtractionSupportCandidateCoversEveryNonzero :
      (A# B# : G3ConstructiveFiniteSupportOperator) →
      (src tgt : G3Wave.SelectedG3State) →
      ¬
      (
        selectedOperatorMatrixElement
          (G3Wave.waveFunctionOperatorSubtraction
            (operator A#)
            (operator B#))
          src
          tgt
        ≡
        0ℚ
      ) →
      MatrixIndexPairListed
        (src ,ᵐ tgt)
        (selectedSubtractionSupportCandidate A# B#)

    selectedSubtractionSupportWitnessFromCandidate :
      (A# B# : G3ConstructiveFiniteSupportOperator) →
      Nat →
      SelectedSubtractionCandidateEntriesAreNonzero A# B# →
      G3FiniteNonzeroMatrixSupportWitness
        (G3Wave.waveFunctionOperatorSubtraction
          (operator A#)
          (operator B#))

    exactFilledDifferencePrimitiveName :
      String

    requestedSubtractionSupportWitnessName :
      String

    requestedSubtractionSupportWitnessType :
      String

    requestedDifferenceNormSymmetryLawType :
      String

    requestedDifferenceNormUltrametricLawType :
      String

    requestedRescalingMinShiftLawType :
      String

    exactNextBracketProductSupportBlocker :
      String

    exactRemainingDifferenceNormLawBlockers :
      List String

    firstNormIndexMissingAfterDifferenceNormLawSurface :
      G3P2OperatorNormIndexMissingLaw

canonicalG3FiniteSupportDifferenceNormLawSurface :
  G3FiniteSupportDifferenceNormLawSurface
canonicalG3FiniteSupportDifferenceNormLawSurface =
  record
    { finiteSupportOperatorSubtype =
        G3ConstructiveFiniteSupportOperator
    ; finiteSupportOperatorSubtypeIsConstructive =
        refl
    ; selectedDifferenceOperatorPrimitive =
        selectedFiniteSupportOperatorDifference
    ; selectedDifferenceOperatorForgetsToSubtraction =
        selectedFiniteSupportOperatorDifferenceForgetsToSubtraction
    ; selectedDifferenceNormIndexPrimitive =
        selectedFiniteSupportOperatorDifferenceNormIndex
    ; selectedDifferenceNormIndexMinimumLaw =
        selectedFiniteSupportOperatorDifferenceNormIndexMinimumLaw
    ; selectedDifferenceNormIndexDegreeSoundness =
        selectedFiniteSupportOperatorDifferenceNormIndexDegreeSoundness
    ; subtractionSymmetryPointwise =
        selectedWaveFunctionOperatorSubtractionSymmetryPointwise
    ; selectedSubtractionSupportCandidate =
        selectedFiniteSupportOperatorSubtractionSupportCandidate
    ; selectedSubtractionSupportCandidateCoversEveryNonzero =
        selectedFiniteSupportOperatorSubtractionCandidateCoversEveryNonzero
    ; selectedSubtractionSupportWitnessFromCandidate =
        selectedFiniteSupportOperatorSubtractionSupportWitnessFromCandidate
    ; exactFilledDifferencePrimitiveName =
        "selectedFiniteSupportOperatorDifferenceNormIndex : (A# B# : G3ConstructiveFiniteSupportOperator) -> G3FiniteNonzeroMatrixSupportWitness (G3Wave.waveFunctionOperatorSubtraction (operator A#) (operator B#)) -> Nat"
    ; requestedSubtractionSupportWitnessName =
        "selectedFiniteSupportOperatorSubtractionSupportWitness"
    ; requestedSubtractionSupportWitnessType =
        "Closed conditionally as selectedFiniteSupportOperatorSubtractionSupportWitnessFromCandidate : (A# B# : G3ConstructiveFiniteSupportOperator) -> Nat -> SelectedSubtractionCandidateEntriesAreNonzero A# B# -> G3FiniteNonzeroMatrixSupportWitness (G3Wave.waveFunctionOperatorSubtraction (operator A#) (operator B#)); unconditional closure needs exact cancellation-filtered support entries"
    ; requestedDifferenceNormSymmetryLawType =
        "(A# B# : G3ConstructiveFiniteSupportOperator) -> (AB# : G3FiniteNonzeroMatrixSupportWitness (G3Wave.waveFunctionOperatorSubtraction (operator A#) (operator B#))) -> (BA# : G3FiniteNonzeroMatrixSupportWitness (G3Wave.waveFunctionOperatorSubtraction (operator B#) (operator A#))) -> selectedFiniteSupportOperatorDifferenceNormIndex A# B# AB# ≡ selectedFiniteSupportOperatorDifferenceNormIndex B# A# BA#"
    ; requestedDifferenceNormUltrametricLawType =
        "(A# B# C# : G3ConstructiveFiniteSupportOperator) -> witnesses for A-B, B-C, and A-C -> selectedFiniteSupportOperatorDifferenceNormIndex A# C# AC# <= UMetric.max (selectedFiniteSupportOperatorDifferenceNormIndex A# B# AB#) (selectedFiniteSupportOperatorDifferenceNormIndex B# C# BC#)"
    ; requestedRescalingMinShiftLawType =
        "selectedFiniteSupportOperatorRescalingMinShift : p2-level rescaling witness -> selectedFiniteSupportOperatorDifferenceNormIndex (rescale k A#) (rescale k B#) witness >= k + selectedFiniteSupportOperatorDifferenceNormIndex A# B# witness, or the repo-accepted min-shift equivalent"
    ; exactNextBracketProductSupportBlocker =
        "selectedFiniteSupportOperatorProductSupportWitness : (A# B# : G3ConstructiveFiniteSupportOperator) -> G3FiniteNonzeroMatrixSupportWitness (G3Wave.operatorCompose (operator A#) (operator B#)); bracket closure then also needs subtraction support for operatorCommutator A B = operatorCompose A B - operatorCompose B A"
    ; exactRemainingDifferenceNormLawBlockers =
        "The finite union support candidate for A# - B# now covers every nonzero difference entry; the exact witness still needs SelectedSubtractionCandidateEntriesAreNonzero, i.e. a cancellation filter/proof that each listed candidate entry is nonzero after subtraction"
        ∷ "Pointwise subtraction antisymmetry exists, but no matrixElementP2Valuation invariance law is available for negated rational matrix elements, so witness-independent norm symmetry is still blocked"
        ∷ "No p2 valuation inequality for rational differences is imported here, so the ultrametric law for selected matrix elements is still unavailable"
        ∷ "No finite-support product/composition support witness exists; this is the exact next support blocker for commutator/bracket laws"
        ∷ "No p2-level rescaling operation on G3ConstructiveFiniteSupportOperator carries a support witness or min-shift valuation law"
        ∷ []
    ; firstNormIndexMissingAfterDifferenceNormLawSurface =
        missingSelectedOperatorDifferenceNormIndexLaws
    }

record G3FiniteSupportMinimumBoundEquivalenceSurface : Setω where
  field
    supportValuationBoundPredicate :
      G3Wave.WaveFunctionOperator →
      List G3SelectedMatrixIndexPair →
      Nat →
      Set

    supportValuationBoundPredicateIsCurrent :
      supportValuationBoundPredicate
      ≡
      SupportValuationsBoundedBelow

    minimumBoundImpliesSupportValuationsBoundedBelow :
      (A : G3Wave.WaveFunctionOperator) →
      (sentinel n : Nat) →
      (support : List G3SelectedMatrixIndexPair) →
      n ≤ finiteSupportMinimumForNonzeroMatrixElementsFromList A sentinel support →
      supportValuationBoundPredicate A support n

    supportValuationsAndSentinelBoundedBelowImpliesMinimumBound :
      (A : G3Wave.WaveFunctionOperator) →
      (sentinel n : Nat) →
      (support : List G3SelectedMatrixIndexPair) →
      n ≤ sentinel →
      supportValuationBoundPredicate A support n →
      n ≤ finiteSupportMinimumForNonzeroMatrixElementsFromList A sentinel support

    exactSentinelSideCondition :
      String

    exactRemainingUnconditionalIffBlocker :
      String

    primitiveSemantics :
      List String

canonicalG3FiniteSupportMinimumBoundEquivalenceSurface :
  G3FiniteSupportMinimumBoundEquivalenceSurface
canonicalG3FiniteSupportMinimumBoundEquivalenceSurface =
  record
    { supportValuationBoundPredicate =
        SupportValuationsBoundedBelow
    ; supportValuationBoundPredicateIsCurrent =
        refl
    ; minimumBoundImpliesSupportValuationsBoundedBelow =
        finiteSupportMinimumBoundImpliesSupportValuationsBoundedBelow
    ; supportValuationsAndSentinelBoundedBelowImpliesMinimumBound =
        supportValuationsAndSentinelBoundedBelowImpliesFiniteSupportMinimumBound
    ; exactSentinelSideCondition =
        "n <= emptySupportSentinel is required for the reverse direction because the current fold includes the sentinel at []"
    ; exactRemainingUnconditionalIffBlocker =
        "To state min >= n iff all support valuations >= n without a sentinel premise, replace the sentinel fold with a nonempty-support minimum or prove the sentinel is neutral/above every relevant bound"
    ; primitiveSemantics =
        "Forward: n <= finiteSupportMinimumForNonzeroMatrixElementsFromList implies every listed support valuation is >= n"
        ∷ "Reverse: if every listed support valuation is >= n and n <= emptySupportSentinel, then the folded finite-support minimum is >= n"
        ∷ "The norm-index degree soundness at the computed minimum does not require the reverse direction or a sentinel bound"
        ∷ []
    }

record G3FiniteSupportFiltrationBracketLawSurface : Setω where
  field
    finiteSupportOperatorSubtype :
      Set

    finiteSupportOperatorSubtypeIsConstructive :
      finiteSupportOperatorSubtype ≡ G3ConstructiveFiniteSupportOperator

    filtrationDegree :
      G3ConstructiveFiniteSupportOperator →
      Nat →
      Set

    normIndexDegreeSoundness :
      (A# : G3ConstructiveFiniteSupportOperator) →
      filtrationDegree A# (selectedFiniteSupportOperatorNormIndex A#)

    requestedBracketLawPrimitiveName :
      String

    requestedBracketLawType :
      String

    exactRemainingBracketLawBlockers :
      List String

    firstNormIndexMissingAfterBracketLawSurface :
      G3P2OperatorNormIndexMissingLaw

canonicalG3FiniteSupportFiltrationBracketLawSurface :
  G3FiniteSupportFiltrationBracketLawSurface
canonicalG3FiniteSupportFiltrationBracketLawSurface =
  record
    { finiteSupportOperatorSubtype =
        G3ConstructiveFiniteSupportOperator
    ; finiteSupportOperatorSubtypeIsConstructive =
        refl
    ; filtrationDegree =
        G3FiniteSupportOperatorFiltrationDegree
    ; normIndexDegreeSoundness =
        selectedFiniteSupportOperatorNormIndexDegreeSoundness
    ; requestedBracketLawPrimitiveName =
        "selectedFiniteSupportOperatorBracketFiltrationLaw"
    ; requestedBracketLawType =
        "(A# B# bracket# : G3ConstructiveFiniteSupportOperator) -> bracket# witnesses the selected bracket [A#,B#] -> (m n : Nat) -> filtrationDegree A# m -> filtrationDegree B# n -> filtrationDegree bracket# (m + n)"
    ; exactRemainingBracketLawBlockers =
        "No selected finite-support product support witness is exposed for G3Wave.operatorCompose (operator A#) (operator B#)"
        ∷ "No selected finite-support bracket constructor is exposed in this file"
        ∷ "No proof is available here that the bracket/subtraction/product of two constructive finite-support operators carries a checked G3FiniteNonzeroMatrixSupportWitness"
        ∷ "No valuation inequality for selected bracket matrix elements has been imported or proved"
        ∷ []
    ; firstNormIndexMissingAfterBracketLawSurface =
        missingSelectedOperatorDifferenceNormIndexLaws
    }

record G3ConstructiveFiniteSupportOperatorNormIndexSurface : Setω where
  field
    finiteSupportOperatorSubtype :
      Set

    finiteSupportOperatorSubtypeIsConstructive :
      finiteSupportOperatorSubtype ≡ G3ConstructiveFiniteSupportOperator

    underlyingOperator :
      finiteSupportOperatorSubtype →
      G3Wave.WaveFunctionOperator

    finiteSupportWitnessForUnderlyingOperator :
      (A# : finiteSupportOperatorSubtype) →
      G3FiniteNonzeroMatrixSupportWitness (underlyingOperator A#)

    selectedOperatorNormIndexPrimitive :
      finiteSupportOperatorSubtype →
      Nat

    selectedOperatorNormIndexMinimumLaw :
      (A# : finiteSupportOperatorSubtype) →
      selectedOperatorNormIndexPrimitive A#
      ≡
      finiteSupportMinimumForNonzeroMatrixElements
        (underlyingOperator A#)
        (finiteSupportWitnessForUnderlyingOperator A#)

    selectedOperatorNormIndexDegreeSoundness :
      (A# : finiteSupportOperatorSubtype) →
      SelectedOperatorP2Degree
        (underlyingOperator A#)
        (selectedOperatorNormIndexPrimitive A#)

    exactFilledPrimitiveName :
      String

    exactDegreeSoundnessPrimitiveName :
      String

    subtypeSemantics :
      List String

    firstNormIndexMissingAfterFiniteSupportSubtype :
      G3P2OperatorNormIndexMissingLaw

    exactNextNormIndexPrimitiveName :
      String

canonicalG3ConstructiveFiniteSupportOperatorNormIndexSurface :
  G3ConstructiveFiniteSupportOperatorNormIndexSurface
canonicalG3ConstructiveFiniteSupportOperatorNormIndexSurface =
  record
    { finiteSupportOperatorSubtype =
        G3ConstructiveFiniteSupportOperator
    ; finiteSupportOperatorSubtypeIsConstructive =
        refl
    ; underlyingOperator =
        operator
    ; finiteSupportWitnessForUnderlyingOperator =
        finiteSupportWitness
    ; selectedOperatorNormIndexPrimitive =
        selectedFiniteSupportOperatorNormIndex
    ; selectedOperatorNormIndexMinimumLaw =
        selectedFiniteSupportOperatorNormIndexMinimumLaw
    ; selectedOperatorNormIndexDegreeSoundness =
        selectedFiniteSupportOperatorNormIndexDegreeSoundness
    ; exactFilledPrimitiveName =
        "selectedFiniteSupportOperatorNormIndex : G3ConstructiveFiniteSupportOperator -> Nat"
    ; exactDegreeSoundnessPrimitiveName =
        "selectedFiniteSupportOperatorNormIndexDegreeSoundness : (A# : G3ConstructiveFiniteSupportOperator) -> SelectedOperatorP2Degree (operator A#) (selectedFiniteSupportOperatorNormIndex A#)"
    ; subtypeSemantics =
        "The subtype bundles a G3Wave.WaveFunctionOperator with an explicit G3FiniteNonzeroMatrixSupportWitness for that operator"
        ∷ "The norm index is finiteSupportMinimumForNonzeroMatrixElements applied to the bundled witness"
        ∷ "The bundled support-cover proof turns every nonzero selected matrix element into a listed support entry"
        ∷ "The finite-list minimum is below every listed valuation, proving the finite-support norm index is a valid selected p2 degree"
        ∷ "This clears the finite-support witness obligation only for operators already carrying constructive finite-support evidence"
        ∷ "It does not construct or imply a global finite-support witness for arbitrary WaveFunctionOperator"
        ∷ []
    ; firstNormIndexMissingAfterFiniteSupportSubtype =
        missingSelectedOperatorDifferenceNormIndexLaws
    ; exactNextNormIndexPrimitiveName =
        "selected finite-support subtraction support witness and difference/bracket norm-index laws"
    }

record G3GlobalFiniteNonzeroMatrixSupportAPI : Setω where
  field
    witnessFor :
      (A : G3Wave.WaveFunctionOperator) →
      G3FiniteNonzeroMatrixSupportWitness A

selectedOperatorNormIndexFromGlobalFiniteSupport :
  G3GlobalFiniteNonzeroMatrixSupportAPI →
  G3Wave.WaveFunctionOperator →
  Nat
selectedOperatorNormIndexFromGlobalFiniteSupport api A =
  finiteSupportMinimumForNonzeroMatrixElements
    A
    (G3GlobalFiniteNonzeroMatrixSupportAPI.witnessFor api A)

selectedOperatorNormIndexMinimumLawFromGlobalFiniteSupport :
  (api : G3GlobalFiniteNonzeroMatrixSupportAPI) →
  (A : G3Wave.WaveFunctionOperator) →
  selectedOperatorNormIndexFromGlobalFiniteSupport api A
  ≡
  finiteSupportMinimumForNonzeroMatrixElements
    A
    (G3GlobalFiniteNonzeroMatrixSupportAPI.witnessFor api A)
selectedOperatorNormIndexMinimumLawFromGlobalFiniteSupport _ _ =
  refl

record G3GlobalFiniteNonzeroMatrixSupportAPIRequest : Setω where
  field
    requestedPrimitiveName :
      String

    requestedPrimitiveType :
      String

    exactReasonItIsStillMissing :
      List String

    conditionalNormIndexPrimitive :
      G3GlobalFiniteNonzeroMatrixSupportAPI →
      G3Wave.WaveFunctionOperator →
      Nat

    conditionalNormIndexMinimumLaw :
      (api : G3GlobalFiniteNonzeroMatrixSupportAPI) →
      (A : G3Wave.WaveFunctionOperator) →
      conditionalNormIndexPrimitive api A
      ≡
      finiteSupportMinimumForNonzeroMatrixElements
        A
        (G3GlobalFiniteNonzeroMatrixSupportAPI.witnessFor api A)

    restrictedFiniteSupportSubtype :
      Set

    restrictedFiniteSupportSubtypeIsConstructive :
      restrictedFiniteSupportSubtype ≡ G3ConstructiveFiniteSupportOperator

    restrictedOperatorForget :
      restrictedFiniteSupportSubtype →
      G3Wave.WaveFunctionOperator

    restrictedFiniteSupportWitness :
      (A# : restrictedFiniteSupportSubtype) →
      G3FiniteNonzeroMatrixSupportWitness (restrictedOperatorForget A#)

    restrictedNormIndexPrimitive :
      restrictedFiniteSupportSubtype →
      Nat

    restrictedNormIndexMinimumLaw :
      (A# : restrictedFiniteSupportSubtype) →
      restrictedNormIndexPrimitive A#
      ≡
      finiteSupportMinimumForNonzeroMatrixElements
        (restrictedOperatorForget A#)
        (restrictedFiniteSupportWitness A#)

    firstNormIndexMissingAfterRestrictedSubtype :
      G3P2OperatorNormIndexMissingLaw

    firstNormIndexMissingAfterRequest :
      G3P2OperatorNormIndexMissingLaw

canonicalG3GlobalFiniteNonzeroMatrixSupportAPIRequest :
  G3GlobalFiniteNonzeroMatrixSupportAPIRequest
canonicalG3GlobalFiniteNonzeroMatrixSupportAPIRequest =
  record
    { requestedPrimitiveName =
        "globalFiniteNonzeroMatrixSupportWitness"
    ; requestedPrimitiveType =
        "(A : G3Wave.WaveFunctionOperator) -> G3FiniteNonzeroMatrixSupportWitness A"
    ; exactReasonItIsStillMissing =
        "The repo exposes G3Wave.WaveFunctionOperator as an arbitrary function WaveFunction -> WaveFunction"
        ∷ "The selected basis carrier is G3Wave.SelectedG3State, which is GL.FactorVec, not an enumerable finite carrier"
        ∷ "A finite support list can be consumed and checked, but no total finite-support extraction function exists for arbitrary WaveFunctionOperator"
        ∷ "Once the global witness is supplied, selectedOperatorNormIndex is definitionally finiteSupportMinimumForNonzeroMatrixElements applied to that witness"
        ∷ "The constructive replacement path is G3ConstructiveFiniteSupportOperator, where each operator carries its own checked finite-support witness"
        ∷ []
    ; conditionalNormIndexPrimitive =
        selectedOperatorNormIndexFromGlobalFiniteSupport
    ; conditionalNormIndexMinimumLaw =
        selectedOperatorNormIndexMinimumLawFromGlobalFiniteSupport
    ; restrictedFiniteSupportSubtype =
        G3ConstructiveFiniteSupportOperator
    ; restrictedFiniteSupportSubtypeIsConstructive =
        refl
    ; restrictedOperatorForget =
        operator
    ; restrictedFiniteSupportWitness =
        finiteSupportWitness
    ; restrictedNormIndexPrimitive =
        selectedFiniteSupportOperatorNormIndex
    ; restrictedNormIndexMinimumLaw =
        selectedFiniteSupportOperatorNormIndexMinimumLaw
    ; firstNormIndexMissingAfterRestrictedSubtype =
        missingSelectedOperatorDifferenceNormIndexLaws
    ; firstNormIndexMissingAfterRequest =
        missingGlobalFiniteNonzeroMatrixSupportWitness
    }

record G3FiniteSupportMinimumForNonzeroMatrixElementsSurface : Setω where
  field
    finiteSupportWitnessType :
      G3Wave.WaveFunctionOperator →
      Set

    finiteSupportWitnessTypeIsCurrent :
      finiteSupportWitnessType ≡ G3FiniteNonzeroMatrixSupportWitness

    finiteSupportMinimumPrimitive :
      (A : G3Wave.WaveFunctionOperator) →
      finiteSupportWitnessType A →
      Nat

    exactFilledPrimitiveName :
      String

    primitiveSemantics :
      List String

    firstNormIndexMissingAfterFiniteSupportMinimum :
      G3P2OperatorNormIndexMissingLaw

    exactNextNormIndexPrimitiveName :
      String

canonicalG3FiniteSupportMinimumForNonzeroMatrixElementsSurface :
  G3FiniteSupportMinimumForNonzeroMatrixElementsSurface
canonicalG3FiniteSupportMinimumForNonzeroMatrixElementsSurface =
  record
    { finiteSupportWitnessType =
        G3FiniteNonzeroMatrixSupportWitness
    ; finiteSupportWitnessTypeIsCurrent =
        refl
    ; finiteSupportMinimumPrimitive =
        finiteSupportMinimumForNonzeroMatrixElements
    ; exactFilledPrimitiveName =
        "finiteSupportMinimumForNonzeroMatrixElements"
    ; primitiveSemantics =
        "The minimum is computable from an explicit finite list of nonzero selectedOperatorMatrixElement indices"
        ∷ "The selected carrier is coordinate-delta over G3Wave.SelectedG3State -> ℚ, not a Hermite or L2 basis"
        ∷ "The witness must prove every listed entry is nonzero and every nonzero matrix element is listed"
        ∷ "No global enumeration of G3Wave.SelectedG3State is assumed, because the current carrier exposes no finite support enumeration API for arbitrary WaveFunctionOperator"
        ∷ []
    ; firstNormIndexMissingAfterFiniteSupportMinimum =
        missingGlobalFiniteNonzeroMatrixSupportWitness
    ; exactNextNormIndexPrimitiveName =
        "globalFiniteNonzeroMatrixSupportWitness supplying a checked finite nonzero matrix support for arbitrary WaveFunctionOperator"
    }

SelectedP2OperatorUltrametric :
  Set (lsuc lzero)
SelectedP2OperatorUltrametric =
  UMetric.Ultrametric SelectedOperator

selectedP2OperatorCompleteIfNatUltrametric :
  (U : SelectedP2OperatorUltrametric) →
  CompleteU.Complete U
selectedP2OperatorCompleteIfNatUltrametric =
  CompleteUNat.completeNatUltrametric

record G3SelectedWaveFunctionBasisCarrierSurface : Setω where
  field
    selectedWaveFunctionBasisCarrier :
      Set

    selectedWaveFunctionBasisCarrierIsSelectedState :
      selectedWaveFunctionBasisCarrier ≡ G3Wave.SelectedG3State

    selectedWaveFunctionCarrier :
      Set

    selectedWaveFunctionCarrierIsCurrent :
      selectedWaveFunctionCarrier ≡ G3Wave.WaveFunction

    selectedOperatorCarrier :
      Set

    selectedOperatorCarrierIsCurrent :
      selectedOperatorCarrier ≡ SelectedOperator

    exactFilledPrimitiveName :
      String

    firstNormIndexMissingAfterCarrier :
      G3P2OperatorNormIndexMissingLaw

    exactNextNormIndexPrimitiveName :
      String

    carrierBoundary :
      List String

canonicalG3SelectedWaveFunctionBasisCarrierSurface :
  G3SelectedWaveFunctionBasisCarrierSurface
canonicalG3SelectedWaveFunctionBasisCarrierSurface =
  record
    { selectedWaveFunctionBasisCarrier =
        SelectedWaveFunctionBasisCarrier
    ; selectedWaveFunctionBasisCarrierIsSelectedState =
        refl
    ; selectedWaveFunctionCarrier =
        G3Wave.WaveFunction
    ; selectedWaveFunctionCarrierIsCurrent =
        refl
    ; selectedOperatorCarrier =
        SelectedOperator
    ; selectedOperatorCarrierIsCurrent =
        refl
    ; exactFilledPrimitiveName =
        "selectedWaveFunctionBasisCarrier : Set"
    ; firstNormIndexMissingAfterCarrier =
        missingGlobalFiniteNonzeroMatrixSupportWitness
    ; exactNextNormIndexPrimitiveName =
        "globalFiniteNonzeroMatrixSupportWitness supplying a checked finite nonzero matrix support for arbitrary WaveFunctionOperator"
    ; carrierBoundary =
        "The selected wave-function basis carrier is fixed to G3Wave.SelectedG3State"
        ∷ "selectedWaveFunctionBasisVector is the coordinatewise delta wave-function over GL.FactorVec"
        ∷ "selectedWaveFunctionBasisCoefficient is evaluation of the selected wave-function at the selected basis state"
        ∷ "selectedOperatorMatrixElement is coefficient evaluation of A applied to the selected basis vector"
        ∷ "finiteSupportMinimumForNonzeroMatrixElements is computable once an explicit finite nonzero support witness is supplied"
        ∷ []
    }

record G3SelectedWaveFunctionBasisVectorSurface : Setω where
  field
    selectedWaveFunctionBasisCarrier :
      Set

    selectedWaveFunctionBasisCarrierIsSelectedState :
      selectedWaveFunctionBasisCarrier ≡ G3Wave.SelectedG3State

    selectedWaveFunctionBasisVectorPrimitive :
      G3Wave.SelectedG3State →
      G3Wave.WaveFunction

    exactFilledPrimitiveName :
      String

    primitiveSemantics :
      List String

    firstNormIndexMissingAfterBasisVector :
      G3P2OperatorNormIndexMissingLaw

    exactNextNormIndexPrimitiveName :
      String

canonicalG3SelectedWaveFunctionBasisVectorSurface :
  G3SelectedWaveFunctionBasisVectorSurface
canonicalG3SelectedWaveFunctionBasisVectorSurface =
  record
    { selectedWaveFunctionBasisCarrier =
        SelectedWaveFunctionBasisCarrier
    ; selectedWaveFunctionBasisCarrierIsSelectedState =
        refl
    ; selectedWaveFunctionBasisVectorPrimitive =
        selectedWaveFunctionBasisVector
    ; exactFilledPrimitiveName =
        "selectedWaveFunctionBasisVector : G3Wave.SelectedG3State -> G3Wave.WaveFunction"
    ; primitiveSemantics =
        "The primitive is a selected point-mass/delta wave-function on G3Wave.SelectedG3State"
        ∷ "G3Wave.SelectedG3State is GL.FactorVec, a 15-coordinate Nat record with constructor GL.v15"
        ∷ "It returns 1ℚ exactly when all 15 selected-state coordinates match by Nat _==_, and 0ℚ otherwise"
        ∷ "The coefficient, matrix-element, p2-valuation, and witness-relative finite-support minimum primitives are closed separately"
        ∷ []
    ; firstNormIndexMissingAfterBasisVector =
        missingGlobalFiniteNonzeroMatrixSupportWitness
    ; exactNextNormIndexPrimitiveName =
        "globalFiniteNonzeroMatrixSupportWitness supplying a checked finite nonzero matrix support for arbitrary WaveFunctionOperator"
    }

record G3SelectedWaveFunctionBasisCoefficientSurface : Setω where
  field
    selectedWaveFunctionBasisCarrier :
      Set

    selectedWaveFunctionBasisCarrierIsSelectedState :
      selectedWaveFunctionBasisCarrier ≡ G3Wave.SelectedG3State

    selectedWaveFunctionBasisCoefficientPrimitive :
      G3Wave.WaveFunction →
      G3Wave.SelectedG3State →
      ℚ

    selectedWaveFunctionBasisCoefficientIsEvaluation :
      (ψ : G3Wave.WaveFunction) →
      (basis : G3Wave.SelectedG3State) →
      selectedWaveFunctionBasisCoefficientPrimitive ψ basis
      ≡
      ψ basis

    basisVectorCoefficientLaw :
      (source target : G3Wave.SelectedG3State) →
      selectedWaveFunctionBasisCoefficientPrimitive
        (selectedWaveFunctionBasisVector source)
        target
      ≡
      selectedWaveFunctionBasisVector source target

    exactFilledPrimitiveName :
      String

    primitiveSemantics :
      List String

    firstNormIndexMissingAfterBasisCoefficient :
      G3P2OperatorNormIndexMissingLaw

    exactNextNormIndexPrimitiveName :
      String

canonicalG3SelectedWaveFunctionBasisCoefficientSurface :
  G3SelectedWaveFunctionBasisCoefficientSurface
canonicalG3SelectedWaveFunctionBasisCoefficientSurface =
  record
    { selectedWaveFunctionBasisCarrier =
        SelectedWaveFunctionBasisCarrier
    ; selectedWaveFunctionBasisCarrierIsSelectedState =
        refl
    ; selectedWaveFunctionBasisCoefficientPrimitive =
        selectedWaveFunctionBasisCoefficient
    ; selectedWaveFunctionBasisCoefficientIsEvaluation =
        λ _ _ → refl
    ; basisVectorCoefficientLaw =
        λ _ _ → refl
    ; exactFilledPrimitiveName =
        "selectedWaveFunctionBasisCoefficient : G3Wave.WaveFunction -> G3Wave.SelectedG3State -> ℚ"
    ; primitiveSemantics =
        "G3Wave.WaveFunction is definitionally G3Wave.SelectedG3State -> ℚ"
        ∷ "The selected basis coefficient is therefore total evaluation at the selected basis state"
        ∷ "No analytic L2 inner product, Hermite carrier, round-to-integer map, or unexposed matrix API is assumed"
        ∷ "The coefficient of selectedWaveFunctionBasisVector source at target reduces definitionally to the delta wave-function value"
        ∷ []
    ; firstNormIndexMissingAfterBasisCoefficient =
        missingGlobalFiniteNonzeroMatrixSupportWitness
    ; exactNextNormIndexPrimitiveName =
        "globalFiniteNonzeroMatrixSupportWitness supplying a checked finite nonzero matrix support for arbitrary WaveFunctionOperator"
    }

record G3SelectedOperatorMatrixElementSurface : Setω where
  field
    selectedWaveFunctionBasisCarrier :
      Set

    selectedWaveFunctionBasisCarrierIsSelectedState :
      selectedWaveFunctionBasisCarrier ≡ G3Wave.SelectedG3State

    selectedOperatorMatrixElementPrimitive :
      G3Wave.WaveFunctionOperator →
      G3Wave.SelectedG3State →
      G3Wave.SelectedG3State →
      ℚ

    selectedOperatorMatrixElementIsCoefficientOfOperatorOnBasisVector :
      (A : G3Wave.WaveFunctionOperator) →
      (source target : G3Wave.SelectedG3State) →
      selectedOperatorMatrixElementPrimitive A source target
      ≡
      selectedWaveFunctionBasisCoefficient
        (A (selectedWaveFunctionBasisVector source))
        target

    exactFilledPrimitiveName :
      String

    primitiveSemantics :
      List String

    firstNormIndexMissingAfterMatrixElement :
      G3P2OperatorNormIndexMissingLaw

    exactNextNormIndexPrimitiveName :
      String

canonicalG3SelectedOperatorMatrixElementSurface :
  G3SelectedOperatorMatrixElementSurface
canonicalG3SelectedOperatorMatrixElementSurface =
  record
    { selectedWaveFunctionBasisCarrier =
        SelectedWaveFunctionBasisCarrier
    ; selectedWaveFunctionBasisCarrierIsSelectedState =
        refl
    ; selectedOperatorMatrixElementPrimitive =
        selectedOperatorMatrixElement
    ; selectedOperatorMatrixElementIsCoefficientOfOperatorOnBasisVector =
        λ _ _ _ → refl
    ; exactFilledPrimitiveName =
        "selectedOperatorMatrixElement : G3Wave.WaveFunctionOperator -> G3Wave.SelectedG3State -> G3Wave.SelectedG3State -> ℚ"
    ; primitiveSemantics =
        "G3Wave.WaveFunctionOperator is definitionally G3Wave.WaveFunction -> G3Wave.WaveFunction"
        ∷ "The selected matrix element applies A to selectedWaveFunctionBasisVector source"
        ∷ "The result is evaluated at target using selectedWaveFunctionBasisCoefficient"
        ∷ "This closes coordinate extraction; p2 valuation and witness-relative finite-support minimum are closed separately"
        ∷ []
    ; firstNormIndexMissingAfterMatrixElement =
        missingGlobalFiniteNonzeroMatrixSupportWitness
    ; exactNextNormIndexPrimitiveName =
        "globalFiniteNonzeroMatrixSupportWitness supplying a checked finite nonzero matrix support for arbitrary WaveFunctionOperator"
    }

record G3MatrixElementP2ValuationSurface : Setω where
  field
    selectedMatrixElementCarrier :
      Set

    selectedMatrixElementCarrierIsRational :
      selectedMatrixElementCarrier ≡ ℚ

    matrixElementP2ValuationPrimitive :
      ℚ →
      Nat

    exactFilledPrimitiveName :
      String

    primitiveSemantics :
      List String

    firstNormIndexMissingAfterValuation :
      G3P2OperatorNormIndexMissingLaw

    exactNextNormIndexPrimitiveName :
      String

canonicalG3MatrixElementP2ValuationSurface :
  G3MatrixElementP2ValuationSurface
canonicalG3MatrixElementP2ValuationSurface =
  record
    { selectedMatrixElementCarrier =
        ℚ
    ; selectedMatrixElementCarrierIsRational =
        refl
    ; matrixElementP2ValuationPrimitive =
        matrixElementP2Valuation
    ; exactFilledPrimitiveName =
        "matrixElementP2Valuation : ℚ -> Nat"
    ; primitiveSemantics =
        "matrixElementP2Valuation q computes bounded p2 exponent of abs numerator minus bounded p2 exponent of denominator, clamped by Nat subtraction"
        ∷ "The numerator is read via Data.Rational.↥_ and absolute-valued with Data.Integer.∣_∣"
        ∷ "The denominator is read via Data.Rational.↧ₙ_"
        ∷ "AIE.vp supplies the repo-local bounded valuation depth; negative rational valuations collapse to zero via _∸_"
        ∷ []
    ; firstNormIndexMissingAfterValuation =
        missingGlobalFiniteNonzeroMatrixSupportWitness
    ; exactNextNormIndexPrimitiveName =
        "globalFiniteNonzeroMatrixSupportWitness supplying a checked finite nonzero matrix support for arbitrary WaveFunctionOperator"
    }

record G3SelectedWaveFunctionBasisVectorAPIRequest : Setω where
  field
    selectedWaveFunctionBasisCarrier :
      Set

    selectedWaveFunctionBasisCarrierIsSelectedState :
      selectedWaveFunctionBasisCarrier ≡ G3Wave.SelectedG3State

    requestedPrimitiveName :
      String

    requestedPrimitiveType :
      String

    requiredDeltaOrPointMassSemantics :
      List String

    rejectedFakeImplementations :
      List String

    firstNormIndexMissingLaw :
      G3P2OperatorNormIndexMissingLaw

    exactFirstMissingPrimitiveName :
      String

canonicalG3SelectedWaveFunctionBasisVectorAPIRequest :
  G3SelectedWaveFunctionBasisVectorAPIRequest
canonicalG3SelectedWaveFunctionBasisVectorAPIRequest =
  record
    { selectedWaveFunctionBasisCarrier =
        SelectedWaveFunctionBasisCarrier
    ; selectedWaveFunctionBasisCarrierIsSelectedState =
        refl
    ; requestedPrimitiveName =
        "selectedWaveFunctionBasisVector"
    ; requestedPrimitiveType =
        "selectedWaveFunctionBasisCarrier -> G3Wave.WaveFunction"
    ; requiredDeltaOrPointMassSemantics =
        "Closed: selectedWaveFunctionBasisVector is a selected point-mass/delta wave-function for the supplied G3Wave.SelectedG3State"
        ∷ "The implementation uses GL.FactorVec constructor GL.v15 and coordinatewise Nat _==_ over all 15 selected-state coordinates"
        ∷ "The vector supports the closed coefficient-by-evaluation primitive and later matrix-element definitions used by selectedOperatorNormIndex"
        ∷ []
    ; rejectedFakeImplementations =
        "G3Wave.zeroψ is not accepted as a basis-vector implementation because it erases the selected state"
        ∷ "G3Wave.oneψ is not accepted as a basis-vector implementation because it is constant and not a point mass"
        ∷ "No Hermite, lattice, or unrelated analytic field is introduced to stand in for a selected wave-function basis"
        ∷ []
    ; firstNormIndexMissingLaw =
        missingGlobalFiniteNonzeroMatrixSupportWitness
    ; exactFirstMissingPrimitiveName =
        "globalFiniteNonzeroMatrixSupportWitness supplying a checked finite nonzero matrix support for arbitrary WaveFunctionOperator"
    }

record G3SelectedP2OperatorNormIndexAPIRequest : Setω where
  field
    requestedPrimitiveName :
      String

    requestedNormIndexType :
      String

    requestedDifferenceNormIndexType :
      String

    requiredBasisAndMatrixElementAPI :
      List String

    requiredMinimumAndValuationLaws :
      List String

    requiredDistanceLaws :
      List String

    firstNormIndexMissingLaw :
      G3P2OperatorNormIndexMissingLaw

    remainingNormIndexMissingLaws :
      List G3P2OperatorNormIndexMissingLaw

canonicalG3SelectedP2OperatorNormIndexAPIRequest :
  G3SelectedP2OperatorNormIndexAPIRequest
canonicalG3SelectedP2OperatorNormIndexAPIRequest =
  record
    { requestedPrimitiveName =
        "G3SelectedP2OperatorNormIndexAPI"
    ; requestedNormIndexType =
        "selectedOperatorNormIndex : WaveFunctionOperator -> Nat, with SelectedOperatorP2Degree A (selectedOperatorNormIndex A)"
    ; requestedDifferenceNormIndexType =
        "selectedOperatorDifferenceNormIndex : (A B : WaveFunctionOperator) -> Nat, definitionally tied to selectedOperatorNormIndex (waveFunctionOperatorSubtraction A B)"
    ; requiredBasisAndMatrixElementAPI =
        "selectedWaveFunctionBasisCarrier : Set = G3Wave.SelectedG3State"
        ∷ "selectedWaveFunctionBasisVector : selectedWaveFunctionBasisCarrier -> WaveFunction"
        ∷ "selectedWaveFunctionBasisCoefficient : WaveFunction -> selectedWaveFunctionBasisCarrier -> ℚ"
        ∷ "closed selectedOperatorMatrixElement : WaveFunctionOperator -> selectedWaveFunctionBasisCarrier -> selectedWaveFunctionBasisCarrier -> ℚ"
        ∷ "matrix elements are tied definitionally to selectedWaveFunctionBasisCoefficient (A (selectedWaveFunctionBasisVector source)) target"
        ∷ []
    ; requiredMinimumAndValuationLaws =
        "matrixElementP2Valuation : ℚ -> Nat, backed by bounded numerator and denominator p2 exponents with Nat subtraction"
        ∷ "matrixElementP2Valuation q = AIE.vp 2 (Data.Integer.∣ Data.Rational.↥ q ∣) ∸ AIE.vp 2 (Data.Rational.↧ₙ q)"
        ∷ "nonzeroMatrixElementSupport : WaveFunctionOperator -> List (selectedWaveFunctionBasisCarrier × selectedWaveFunctionBasisCarrier), or an equivalent finite support witness"
        ∷ "finiteSupportMinimumForNonzeroMatrixElements computes the minimum matrixElementP2Valuation over nonzero support"
        ∷ "globalFiniteNonzeroMatrixSupportWitness supplies such a witness for every arbitrary WaveFunctionOperator"
        ∷ "selectedOperatorNormIndexMinimumLaw is definitional once selectedOperatorNormIndex is built from that global witness"
        ∷ []
    ; requiredDistanceLaws =
        "selectedOperatorNormIndexDegreeSoundness : (A : WaveFunctionOperator) -> SelectedOperatorP2Degree A (selectedOperatorNormIndex A)"
        ∷ "selectedOperatorNormIdentityZero : selectedOperatorDifferenceNormIndex A A == zero, with the accepted zero/equality convention"
        ∷ "selectedOperatorDifferenceNormSymmetry : selectedOperatorDifferenceNormIndex A B == selectedOperatorDifferenceNormIndex B A"
        ∷ "selectedOperatorDifferenceNormUltrametric : selectedOperatorDifferenceNormIndex A C <= max (selectedOperatorDifferenceNormIndex A B) (selectedOperatorDifferenceNormIndex B C)"
        ∷ []
    ; firstNormIndexMissingLaw =
        missingGlobalFiniteNonzeroMatrixSupportWitness
    ; remainingNormIndexMissingLaws =
        missingGlobalFiniteNonzeroMatrixSupportWitness
        ∷ missingSelectedOperatorNormIndexMinimumLaw
        ∷ missingSelectedOperatorNormIndexDegreeSoundness
        ∷ missingSelectedOperatorDifferenceNormIndexLaws
        ∷ []
    }

record G3SelectedP2OperatorUltrametricAPI : Setω where
  field
    operatorCarrier :
      Set

    operatorCarrierIsSelected :
      operatorCarrier ≡ SelectedOperator

    p2OperatorUltrametric :
      SelectedP2OperatorUltrametric

    operatorDistancePrimitive :
      G3Norm.G3SelectedP2OperatorDistancePrimitive

    p2OperatorUltrametricIsFromDistancePrimitive :
      p2OperatorUltrametric
      ≡
      G3Norm.selectedP2OperatorUltrametricFromDistancePrimitive
        operatorDistancePrimitive

    distanceSemantics :
      List String

    distanceUsesSelectedNormIndex :
      List String

    normMetricSurface :
      G3Norm.G3SelectedP2AdicNormMetricSurface

selectedP2OperatorUltrametricAPIFromDistancePrimitive :
  G3Norm.G3SelectedP2OperatorDistancePrimitive →
  G3SelectedP2OperatorUltrametricAPI
selectedP2OperatorUltrametricAPIFromDistancePrimitive distance =
  record
    { operatorCarrier =
        SelectedOperator
    ; operatorCarrierIsSelected =
        refl
    ; p2OperatorUltrametric =
        G3Norm.selectedP2OperatorUltrametricFromDistancePrimitive
          distance
    ; operatorDistancePrimitive =
        distance
    ; p2OperatorUltrametricIsFromDistancePrimitive =
        refl
    ; distanceSemantics =
        "Selected p2 operator ultrametric is constructed from G3SelectedP2OperatorDistancePrimitive"
        ∷ "The distance primitive must supply identity, symmetry, and ultrametric laws on selected WaveFunctionOperator"
        ∷ []
    ; distanceUsesSelectedNormIndex =
        G3Norm.G3SelectedP2OperatorDistancePrimitive.distanceTiedToSelectedNormIndex
          distance
    ; normMetricSurface =
        G3Norm.canonicalG3SelectedP2AdicNormMetricSurface
    }

record G3SelectedP2RescaledBoostCauchyZeroLimitAPI
  (api : G3SelectedP2OperatorUltrametricAPI) : Setω where
  open G3SelectedP2OperatorUltrametricAPI api

  field
    rescalingPrimitive :
      G3Norm.G3SelectedP2OperatorRescalingPrimitive
        operatorDistancePrimitive

    rescaledBoostIsCauchy :
      (d : G3Concrete.G3SpatialDirection) →
      CompleteU.Cauchy p2OperatorUltrametric

    rescaledBoostCauchyIsTheRescaledSequence :
      (d : G3Concrete.G3SpatialDirection) →
      CompleteU.Cauchy.seq (rescaledBoostIsCauchy d)
      ≡
      G3Norm.G3SelectedP2OperatorRescalingPrimitive.rescaledBoostSequence
        rescalingPrimitive d

    rescaledBoostLimitIsSelectedZeroOperator :
      (d : G3Concrete.G3SpatialDirection) →
      CompleteU.Complete.limit
        (CompleteUNat.completeNatUltrametric p2OperatorUltrametric)
        (rescaledBoostIsCauchy d)
      ≡
      G3Norm.G3SelectedP2OperatorRescalingPrimitive.zeroLimitOperator
        rescalingPrimitive

    exactCauchyZeroLimitSemantics :
      List String

record G3SelectedP2LimitConvergencePrimitive
  (api : G3SelectedP2OperatorUltrametricAPI) : Setω where
  open G3SelectedP2OperatorUltrametricAPI api

  field
    rescaledBoostSequence :
      G3Concrete.G3SpatialDirection →
      Nat →
      SelectedOperator

    rescaledBoostSequenceSemantics :
      List String

    rescaledBoostIsCauchy :
      (d : G3Concrete.G3SpatialDirection) →
      CompleteU.Cauchy p2OperatorUltrametric

    rescaledBoostCauchyIsTheSequence :
      (d : G3Concrete.G3SpatialDirection) →
      CompleteU.Cauchy.seq (rescaledBoostIsCauchy d)
      ≡
      rescaledBoostSequence d

    rescaledBoostLimit :
      (d : G3Concrete.G3SpatialDirection) →
      SelectedOperator

    rescaledBoostLimitIsZeroOperator :
      List String

    rescaledBoostLimitIsCompleteNatLimit :
      (d : G3Concrete.G3SpatialDirection) →
      rescaledBoostLimit d
      ≡
      CompleteU.Complete.limit
        (CompleteUNat.completeNatUltrametric p2OperatorUltrametric)
        (rescaledBoostIsCauchy d)

selectedP2LimitConvergencePrimitiveFromCauchyZeroLimitAPI :
  (api : G3SelectedP2OperatorUltrametricAPI) →
  G3SelectedP2RescaledBoostCauchyZeroLimitAPI api →
  G3SelectedP2LimitConvergencePrimitive api
selectedP2LimitConvergencePrimitiveFromCauchyZeroLimitAPI api cauchyZero =
  let
    open G3SelectedP2OperatorUltrametricAPI api
    open G3SelectedP2RescaledBoostCauchyZeroLimitAPI cauchyZero
  in
  record
    { rescaledBoostSequence =
        G3Norm.G3SelectedP2OperatorRescalingPrimitive.rescaledBoostSequence
          rescalingPrimitive
    ; rescaledBoostSequenceSemantics =
        G3Norm.G3SelectedP2OperatorRescalingPrimitive.exactRescalingSemantics
          rescalingPrimitive
    ; rescaledBoostIsCauchy =
        rescaledBoostIsCauchy
    ; rescaledBoostCauchyIsTheSequence =
        rescaledBoostCauchyIsTheRescaledSequence
    ; rescaledBoostLimit =
        λ _ →
          G3Norm.G3SelectedP2OperatorRescalingPrimitive.zeroLimitOperator
            rescalingPrimitive
    ; rescaledBoostLimitIsZeroOperator =
        "Limit operator is the zeroLimitOperator of G3SelectedP2OperatorRescalingPrimitive"
        ∷ "The rescaling primitive must prove zeroLimitOperatorIsSelectedZero"
        ∷ exactCauchyZeroLimitSemantics
    ; rescaledBoostLimitIsCompleteNatLimit =
        λ d →
          sym (rescaledBoostLimitIsSelectedZeroOperator d)
    }

record G3P2LimitConvergenceFailClosedReceipt : Setω where
  field
    status :
      G3P2LimitConvergenceStatus

    selectedOperatorCarrier :
      Set

    selectedOperatorCarrierIsCurrent :
      selectedOperatorCarrier ≡ SelectedOperator

    natUltrametricCompletenessAvailable :
      (U : SelectedP2OperatorUltrametric) →
      CompleteU.Complete U

    normMetricSurface :
      G3Norm.G3SelectedP2AdicNormMetricSurface

    distanceConstructionAttempt :
      G3Norm.G3SelectedP2OperatorDistanceConstructionAttempt

    basisCarrierSurface :
      G3SelectedWaveFunctionBasisCarrierSurface

    basisVectorSurface :
      G3SelectedWaveFunctionBasisVectorSurface

    basisCoefficientSurface :
      G3SelectedWaveFunctionBasisCoefficientSurface

    matrixElementSurface :
      G3SelectedOperatorMatrixElementSurface

    basisVectorAPIRequest :
      G3SelectedWaveFunctionBasisVectorAPIRequest

    matrixElementP2ValuationSurface :
      G3MatrixElementP2ValuationSurface

    finiteSupportMinimumSurface :
      G3FiniteSupportMinimumForNonzeroMatrixElementsSurface

    finiteSupportMinimumBoundEquivalenceSurface :
      G3FiniteSupportMinimumBoundEquivalenceSurface

    finiteSupportOperatorNormIndexSurface :
      G3ConstructiveFiniteSupportOperatorNormIndexSurface

    finiteSupportDifferenceNormLawSurface :
      G3FiniteSupportDifferenceNormLawSurface

    finiteSupportFiltrationBracketLawSurface :
      G3FiniteSupportFiltrationBracketLawSurface

    normIndexAPIRequest :
      G3SelectedP2OperatorNormIndexAPIRequest

    globalFiniteSupportAPIRequest :
      G3GlobalFiniteNonzeroMatrixSupportAPIRequest

    exactReducedPrimitiveName :
      String

    selectedOperatorUltrametricFromDistancePrimitiveAvailable :
      G3Norm.G3SelectedP2OperatorDistancePrimitive →
      G3SelectedP2OperatorUltrametricAPI

    selectedLimitPrimitiveFromCauchyZeroLimitAvailable :
      (api : G3SelectedP2OperatorUltrametricAPI) →
      G3SelectedP2RescaledBoostCauchyZeroLimitAPI api →
      G3SelectedP2LimitConvergencePrimitive api

    firstMissing :
      G3P2LimitConvergenceMissingPrimitive

    firstMissingIsSelectedOperatorNormIndexFunction :
      firstMissing ≡ missingSelectedOperatorNormIndexFunction

    normIndexFirstMissingLaw :
      G3P2OperatorNormIndexMissingLaw

    normIndexFirstMissingLawIsRequestFirst :
      normIndexFirstMissingLaw
      ≡
      G3SelectedP2OperatorNormIndexAPIRequest.firstNormIndexMissingLaw
        normIndexAPIRequest

    basisCarrierPrimitiveFilled :
      G3SelectedWaveFunctionBasisCarrierSurface.firstNormIndexMissingAfterCarrier
        basisCarrierSurface
      ≡
      normIndexFirstMissingLaw

    basisVectorRequestIsExactFirstNormIndexMissing :
      G3SelectedWaveFunctionBasisVectorAPIRequest.firstNormIndexMissingLaw
        basisVectorAPIRequest
      ≡
      normIndexFirstMissingLaw

    basisVectorPrimitiveFilled :
      G3SelectedWaveFunctionBasisVectorSurface.firstNormIndexMissingAfterBasisVector
        basisVectorSurface
      ≡
      normIndexFirstMissingLaw

    basisCoefficientPrimitiveFilled :
      G3SelectedWaveFunctionBasisCoefficientSurface.firstNormIndexMissingAfterBasisCoefficient
        basisCoefficientSurface
      ≡
      normIndexFirstMissingLaw

    matrixElementPrimitiveFilled :
      G3SelectedOperatorMatrixElementSurface.firstNormIndexMissingAfterMatrixElement
        matrixElementSurface
      ≡
      normIndexFirstMissingLaw

    finiteSupportSubtypeNextMissingIsDifferenceLaws :
      G3ConstructiveFiniteSupportOperatorNormIndexSurface.firstNormIndexMissingAfterFiniteSupportSubtype
        finiteSupportOperatorNormIndexSurface
      ≡
      missingSelectedOperatorDifferenceNormIndexLaws

    globalWitnessRequestStillNamesArbitraryOperatorBlocker :
      G3GlobalFiniteNonzeroMatrixSupportAPIRequest.firstNormIndexMissingAfterRequest
        globalFiniteSupportAPIRequest
      ≡
      missingGlobalFiniteNonzeroMatrixSupportWitness

    exactNormIndexFirstMissingPrimitiveName :
      String

    remainingMissing :
      List G3P2LimitConvergenceMissingPrimitive

    positiveEvidence :
      List String

    nonPromotionBoundary :
      List String

canonicalG3P2LimitConvergenceFailClosedReceipt :
  G3P2LimitConvergenceFailClosedReceipt
canonicalG3P2LimitConvergenceFailClosedReceipt =
  record
    { status =
        selectedP2LimitReducedToNatUltrametricCompletenessNoPromotion
    ; selectedOperatorCarrier =
        SelectedOperator
    ; selectedOperatorCarrierIsCurrent =
        refl
    ; natUltrametricCompletenessAvailable =
        selectedP2OperatorCompleteIfNatUltrametric
    ; normMetricSurface =
        G3Norm.canonicalG3SelectedP2AdicNormMetricSurface
    ; distanceConstructionAttempt =
        G3Norm.canonicalSelectedP2OperatorDistanceConstructionAttempt
    ; basisCarrierSurface =
        canonicalG3SelectedWaveFunctionBasisCarrierSurface
    ; basisVectorSurface =
        canonicalG3SelectedWaveFunctionBasisVectorSurface
    ; basisCoefficientSurface =
        canonicalG3SelectedWaveFunctionBasisCoefficientSurface
    ; matrixElementSurface =
        canonicalG3SelectedOperatorMatrixElementSurface
    ; basisVectorAPIRequest =
        canonicalG3SelectedWaveFunctionBasisVectorAPIRequest
    ; matrixElementP2ValuationSurface =
        canonicalG3MatrixElementP2ValuationSurface
    ; finiteSupportMinimumSurface =
        canonicalG3FiniteSupportMinimumForNonzeroMatrixElementsSurface
    ; finiteSupportMinimumBoundEquivalenceSurface =
        canonicalG3FiniteSupportMinimumBoundEquivalenceSurface
    ; finiteSupportOperatorNormIndexSurface =
        canonicalG3ConstructiveFiniteSupportOperatorNormIndexSurface
    ; finiteSupportDifferenceNormLawSurface =
        canonicalG3FiniteSupportDifferenceNormLawSurface
    ; finiteSupportFiltrationBracketLawSurface =
        canonicalG3FiniteSupportFiltrationBracketLawSurface
    ; normIndexAPIRequest =
        canonicalG3SelectedP2OperatorNormIndexAPIRequest
    ; globalFiniteSupportAPIRequest =
        canonicalG3GlobalFiniteNonzeroMatrixSupportAPIRequest
    ; exactReducedPrimitiveName =
        "(api : G3SelectedP2OperatorUltrametricAPI) -> G3SelectedP2LimitConvergencePrimitive api"
    ; selectedOperatorUltrametricFromDistancePrimitiveAvailable =
        selectedP2OperatorUltrametricAPIFromDistancePrimitive
    ; selectedLimitPrimitiveFromCauchyZeroLimitAvailable =
        selectedP2LimitConvergencePrimitiveFromCauchyZeroLimitAPI
    ; firstMissing =
        missingSelectedOperatorNormIndexFunction
    ; firstMissingIsSelectedOperatorNormIndexFunction =
        refl
    ; normIndexFirstMissingLaw =
        missingGlobalFiniteNonzeroMatrixSupportWitness
    ; normIndexFirstMissingLawIsRequestFirst =
        refl
    ; basisCarrierPrimitiveFilled =
        refl
    ; basisVectorRequestIsExactFirstNormIndexMissing =
        refl
    ; basisVectorPrimitiveFilled =
        refl
    ; basisCoefficientPrimitiveFilled =
        refl
    ; matrixElementPrimitiveFilled =
        refl
    ; finiteSupportSubtypeNextMissingIsDifferenceLaws =
        refl
    ; globalWitnessRequestStillNamesArbitraryOperatorBlocker =
        refl
    ; exactNormIndexFirstMissingPrimitiveName =
        "globalFiniteNonzeroMatrixSupportWitness supplying the witness consumed by finiteSupportMinimumForNonzeroMatrixElements"
    ; remainingMissing =
        missingSelectedOperatorNormIndexFunction
        ∷ missingSelectedOperatorDifferenceNormIndex
        ∷ missingSelectedOperatorNormIdentityZero
        ∷ missingSelectedOperatorDifferenceNormSymmetry
        ∷ missingSelectedOperatorDifferenceNormUltrametric
        ∷ missingSelectedP2OperatorDistancePrimitive
        ∷ missingSelectedP2OperatorRescalingPrimitive
        ∷ missingSelectedOperatorRescalingDistanceBound
        ∷ missingSelectedP2RescaledBoostSequence
        ∷ missingSelectedP2RescaledBoostCauchyWitness
        ∷ missingSelectedP2RescaledBoostZeroLimitWitness
        ∷ []
    ; positiveEvidence =
        "DASHI.Geometry.CompleteUltrametricNat.completeNatUltrametric proves completeness for any Nat-valued ultrametric"
        ∷ "The selected carrier for the limit lane is exactly G3Wave.WaveFunctionOperator"
        ∷ "G3P2AdicNormMetricSurface already binds selected P/H/K/mass to Nat-valued p2 norm-index evidence"
        ∷ "G3Wave.waveFunctionOperatorSubtraction gives the candidate difference operator A - B"
        ∷ "The selected p2 distance construction attempt is narrowed to exact norm-index, identity, symmetry, ultrametric, and rescaling-bound blockers"
        ∷ "The selectedOperatorNormIndex blocker is now narrowed through selectedWaveFunctionBasisCarrier = G3Wave.SelectedG3State"
        ∷ "selectedWaveFunctionBasisVector is now closed as a coordinatewise GL.FactorVec delta wave-function"
        ∷ "selectedWaveFunctionBasisCoefficient is now closed as evaluation of G3Wave.WaveFunction at the selected basis state"
        ∷ "selectedOperatorMatrixElement is now closed as selectedWaveFunctionBasisCoefficient (A (selectedWaveFunctionBasisVector source)) target"
        ∷ "matrixElementP2Valuation is now closed as bounded numerator p2 exponent minus bounded denominator p2 exponent, clamped by Nat subtraction"
        ∷ "finiteSupportMinimumForNonzeroMatrixElements is now closed relative to an explicit G3FiniteNonzeroMatrixSupportWitness"
        ∷ "The finite-support min-bound equivalence is closed with the explicit sentinel side condition n <= emptySupportSentinel"
        ∷ "selectedFiniteSupportOperatorNormIndex is now closed for G3ConstructiveFiniteSupportOperator"
        ∷ "selectedFiniteSupportOperatorNormIndexDegreeSoundness is now closed for G3ConstructiveFiniteSupportOperator"
        ∷ "selectedFiniteSupportOperatorDifferenceNormIndex is now closed relative to an explicit support witness for G3Wave.waveFunctionOperatorSubtraction (operator A#) (operator B#)"
        ∷ "selectedFiniteSupportOperatorSubtractionSupportCandidate is now the union of the two finite support witnesses and covers every nonzero selected matrix element of A# - B#"
        ∷ "selectedFiniteSupportOperatorSubtractionSupportWitnessFromCandidate now constructs the exact subtraction witness from the candidate once cancellation-filtered nonzero entries are supplied"
        ∷ "G3Wave.waveFunctionOperatorNegatedDifferencePointwise supplies pointwise subtraction antisymmetry; norm-level symmetry still needs valuation invariance under rational negation and compatible exact support witnesses"
        ∷ "The finite-support filtration bracket-law surface is named, with bracket/support-closure and valuation bounds left explicit"
        ∷ "The exact next bracket/product support blocker is selectedFiniteSupportOperatorProductSupportWitness for G3Wave.operatorCompose"
        ∷ "The finite-support subtype path clears the global witness blocker only for operators carrying explicit finite-support evidence"
        ∷ "The arbitrary WaveFunctionOperator global witness request remains fail-closed and honest"
        ∷ "A selected p2 operator ultrametric is now constructible from G3SelectedP2OperatorDistancePrimitive"
        ∷ "A selected p2 limit primitive is now constructible from G3SelectedP2RescaledBoostCauchyZeroLimitAPI"
        ∷ "The old missingP2LimitConvergencePrimitive is now reduced to exact selected operator distance, rescaling, Cauchy, and zero-limit witnesses"
        ∷ []
    ; nonPromotionBoundary =
        "No p2 operator distance is fabricated here"
        ∷ "No arbitrary selected operator norm-index function is fabricated here"
        ∷ "No global finite-support witness for arbitrary WaveFunctionOperator is fabricated here; the closed path is restricted to G3ConstructiveFiniteSupportOperator"
        ∷ "No arbitrary selected operator norm-index degree-soundness law is fabricated here; the promoted soundness path is restricted to G3ConstructiveFiniteSupportOperator"
        ∷ "No unconditional selected finite-support subtraction support witness, product support witness, or bracket law is fabricated here"
        ∷ "No zeroψ/oneψ constant wave-function is promoted as a selected basis vector; the basis vector is coordinate-sensitive"
        ∷ "No identity/symmetry/ultrametric law for a difference norm is fabricated here beyond the witness-relative difference norm-index primitive and the finite subtraction support-cover candidate"
        ∷ "No p2-level rescaling operation on WaveFunctionOperator is fabricated here"
        ∷ "No rescaling distance bound is fabricated here"
        ∷ "No rescaled boost Cauchy or convergence-to-zero witness is fabricated here"
        ∷ "No SchrodingerPoincareToGalileiContractionCarrier is inhabited here"
        ∷ []
    }
