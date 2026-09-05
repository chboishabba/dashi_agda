module DASHI.Analysis.NonArchimedeanOneOrbitTraceCancellationExact where

------------------------------------------------------------------------
-- ONE-ORBIT TRACE CUTSET
--
-- After the negative-orbit conjugation weld, the pair is not two independent
-- weights:
--
--   W2 = conjugate(W1).
--
-- Therefore the missing cancellation theorem W1 + W2 = 0 is exactly the
-- one-orbit conjugation-trace statement
--
--   W1 + conjugate(W1) = 0.
--
-- This is the minimal signed producer.  Combined with the already-owned paired
-- product W1*W2=2, the existing minus-two compiler closes both orbit squares.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

record ConjugateTraceCancellation : Set₁ where
  field
    Scalar : Set
    zero : Scalar
    add : Scalar → Scalar → Scalar
    conjugate : Scalar → Scalar

    W1 W2 : Scalar

    negativeOrbitWeightIsConjugate :
      W2 ≡ conjugate W1

    oneOrbitTraceZero :
      add W1 (conjugate W1) ≡ zero

open ConjugateTraceCancellation public

pairedOrbitCancellation :
  (data : ConjugateTraceCancellation) →
  add data (W1 data) (W2 data) ≡ zero data
pairedOrbitCancellation data =
  trans
    (cong (add data (W1 data))
      (negativeOrbitWeightIsConjugate data))
    (oneOrbitTraceZero data)

record OneOrbitTraceBoundary : Set where
  constructor oneOrbitTraceBoundary
  field
    twoIndependentSignedWeightsRemain : Bool
    negativeOrbitConjugationWeldReducesPair : Bool
    oneOrbitTraceZeroIsCriticalSignedLeaf : Bool
    explicitComplexPhaseValuesRequired : Bool
    pairedProductTwoStillIndependent : Bool

canonicalOneOrbitTraceBoundary : OneOrbitTraceBoundary
canonicalOneOrbitTraceBoundary =
  oneOrbitTraceBoundary false true true false true

oneOrbitTraceIsCriticalLeaf :
  OneOrbitTraceBoundary.oneOrbitTraceZeroIsCriticalSignedLeaf
    canonicalOneOrbitTraceBoundary
  ≡ true
oneOrbitTraceIsCriticalLeaf = refl
