module DASHI.Moonshine.Monster3BFiniteSchrodingerDeltaExtractionExact where

------------------------------------------------------------------------
-- DELTA-LINE EXTRACTION FROM A NONZERO HEISENBERG-INVARIANT SUBSPACE
--
-- Given f in W and one selected point s with norm-qualified f(s) != 0:
--   1. the modulation-derived point projector stays in W;
--   2. it evaluates to 729 f(s) at s and 0 at every explicitly different x;
--   3. the exact cyclotomic inverse of f(s), together with 1/729, normalises
--      that projected vector to the literal comparison-defined delta_s;
--   4. pointwise extensional closure transports membership to delta_s.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl; sym; trans)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Moonshine.Monster3BCyclotomicLinearAlgebraExact as L
import DASHI.Moonshine.Monster3BCyclotomicNonzeroInverseExact as Inv
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteSchrodingerFunctionModuleExact as V
import DASHI.Moonshine.Monster3BFiniteSchrodingerPointProjectorExact as Point
import DASHI.Moonshine.Monster3BFiniteSchrodingerPointProjectorEvaluationExact as Eval
import DASHI.Moonshine.Monster3BFiniteSchrodingerProjector729Exact as P729
import DASHI.Moonshine.Monster3BFiniteX6ConstructiveComparisonExact as Compare

------------------------------------------------------------------------
-- 1. Delta defined by the exact same equality/difference decision consumed by
--    the off-point projector theorem.
------------------------------------------------------------------------

comparisonDelta : H.X6 → V.SchrodingerFunction
comparisonDelta selected x with Compare.compareX6 selected x
... | Compare.sameX6 refl = C3.one
... | Compare.differentX6 difference = C3.zero

------------------------------------------------------------------------
-- 2. A nonzero subspace witness names the actual selected coefficient and
--    carries its norm-qualified inverse receipt.
------------------------------------------------------------------------

record NonzeroInvariantVector
    {Member : V.SchrodingerFunction → Set}
    (inv : V.HeisenbergInvariantSubspace Member) : Set where
  constructor nonzero-invariant-vector
  field
    vector : V.SchrodingerFunction
    vectorMember : Member vector
    selected : H.X6
    selectedAmplitude : Inv.NonzeroCyclotomicAmplitude
    selectedAmplitudeIsValue :
      Inv.amplitude selectedAmplitude ≡ vector selected
open NonzeroInvariantVector public

------------------------------------------------------------------------
-- 3. Exact rational 1/729 normalisation.
------------------------------------------------------------------------

reciprocal729 : ℚ
reciprocal729 = 1ℚ / 729

reciprocal729Exact : reciprocal729 * 729 ≡ 1ℚ
reciprocal729Exact = solve []

normalizer :
  ∀ {Member inv} →
  NonzeroInvariantVector {Member} inv → C3.Cyclotomic3
normalizer witness =
  L.scale reciprocal729 (Inv.inverse (selectedAmplitude witness))

normalizerCancels729Amplitude :
  ∀ {Member inv}
    (witness : NonzeroInvariantVector {Member} inv) →
  C3.multiply
    (normalizer witness)
    (L.scale 729 (vector witness (selected witness)))
  ≡ C3.one
normalizerCancels729Amplitude witness =
  let
    aWitness = selectedAmplitude witness
    a = Inv.amplitude aWitness
    aInv = Inv.inverse aWitness
  in
  trans
    (L.multiplyScaleLeft reciprocal729 aInv
      (L.scale 729 (vector witness (selected witness))))
    (trans
      (cong (L.scale reciprocal729)
        (trans
          (L.multiplyScaleRight 729 aInv
            (vector witness (selected witness)))
          (trans
            (cong (L.scale 729)
              (trans
                (L.multiplyCommutative aInv (vector witness (selected witness)))
                (trans
                  (cong (λ z → C3.multiply z aInv)
                    (sym (selectedAmplitudeIsValue witness)))
                  (Inv.rightInverse aWitness))))
            refl)))
      (trans
        (L.scaleScale reciprocal729 729 C3.one)
        (trans
          (cong (λ r → L.scale r C3.one) reciprocal729Exact)
          refl)))

------------------------------------------------------------------------
-- 4. Normalised derived projector agrees pointwise with delta_s.
------------------------------------------------------------------------

normalisedPointProjection :
  ∀ {Member inv} →
  NonzeroInvariantVector {Member} inv → V.SchrodingerFunction
normalisedPointProjection witness =
  V.cyclotomicScaleFunction
    (normalizer witness)
    (Point.pointProjector (selected witness) (vector witness))

normalisedProjectionIsDeltaPointwise :
  ∀ {Member inv}
    (witness : NonzeroInvariantVector {Member} inv) →
  V.PointwiseEqual
    (normalisedPointProjection witness)
    (comparisonDelta (selected witness))
normalisedProjectionIsDeltaPointwise witness x
  with Compare.compareX6 (selected witness) x
... | Compare.sameX6 refl =
  trans
    (cong (C3.multiply (normalizer witness))
      (trans
        (Eval.pointProjectorSelected
          (selected witness) (vector witness))
        (P729.sixTriplesAre729
          (vector witness (selected witness)))))
    (normalizerCancels729Amplitude witness)
... | Compare.differentX6 difference =
  trans
    (cong (C3.multiply (normalizer witness))
      (Eval.pointProjectorOffPoint
        (selected witness) x (vector witness) difference))
    (L.zeroActsLeft (normalizer witness))

------------------------------------------------------------------------
-- 5. Membership extraction: all operations are already justified by the
--    invariant-subspace interface; the final step is pointwise equality.
------------------------------------------------------------------------

deltaLineMember :
  ∀ {Member}
    (inv : V.HeisenbergInvariantSubspace Member) →
    (witness : NonzeroInvariantVector inv) →
  Member (comparisonDelta (selected witness))
deltaLineMember inv witness =
  V.closedUnderPointwiseEquality inv
    (normalisedPointProjection witness)
    (comparisonDelta (selected witness))
    (V.closedUnderCyclotomicScaling inv
      (normalizer witness)
      (Point.pointProjector (selected witness) (vector witness))
      (Point.pointProjectorPreservesInvariantSubspace inv
        (selected witness) (vector witness) (vectorMember witness)))
    (normalisedProjectionIsDeltaPointwise witness)

record DeltaExtractionBoundary : Set where
  constructor deltaExtractionBoundary
  field
    comparisonDefinedDeltaConstructed : Bool
    exactReciprocal729Used : Bool
    nonzeroCyclotomicNormalisationUsed : Bool
    derivedProjectorNormalisesPointwiseToDelta : Bool
    invariantSubspaceContainsSelectedDeltaLine : Bool
    fullSchrodingerIrreducibilityProvedHere : Bool
open DeltaExtractionBoundary public

canonicalDeltaExtractionBoundary : DeltaExtractionBoundary
canonicalDeltaExtractionBoundary =
  deltaExtractionBoundary true true true true true false
