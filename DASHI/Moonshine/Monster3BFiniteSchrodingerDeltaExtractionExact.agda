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

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

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

deltaFromComparison : ∀ {s x} → Compare.X6Comparison s x → C3.Cyclotomic3
deltaFromComparison (Compare.sameX6 refl) = C3.one
deltaFromComparison (Compare.differentX6 difference) = C3.zero

comparisonDelta : H.X6 → V.SchrodingerFunction
comparisonDelta selected x = deltaFromComparison (Compare.compareX6 selected x)

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
reciprocal729 = + 1 / 729

reciprocal729Exact : reciprocal729 * P729.729ℚ ≡ 1ℚ
reciprocal729Exact = refl

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
    (L.scale P729.729ℚ (vector witness (selected witness)))
  ≡ C3.one
normalizerCancels729Amplitude witness =
  let
    aWitness = selectedAmplitude witness
    a = Inv.amplitude aWitness
    aInv = Inv.inverse aWitness
  in
  trans
    (L.multiplyScaleLeft reciprocal729 aInv
      (L.scale P729.729ℚ (vector witness (selected witness))))
    (trans
      (cong (L.scale reciprocal729)
        (trans
          (L.multiplyScaleRight P729.729ℚ aInv
            (vector witness (selected witness)))
          (trans
            (cong (L.scale P729.729ℚ)
              (trans
                (L.multiplyCommutative aInv (vector witness (selected witness)))
                (trans
                  (cong (λ z → C3.multiply z aInv)
                    (sym (selectedAmplitudeIsValue witness)))
                  (Inv.rightInverse aWitness))))
            refl)))
      (trans
        (L.scaleScale reciprocal729 P729.729ℚ C3.one)
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

projectionMatchesDelta :
  ∀ {Member inv} (witness : NonzeroInvariantVector {Member} inv) (x : H.X6)
  (cmp : Compare.X6Comparison (selected witness) x) →
  normalisedPointProjection witness x ≡ deltaFromComparison cmp
projectionMatchesDelta witness .(selected witness) (Compare.sameX6 refl) =
  trans
    (cong (C3.multiply (normalizer witness))
      (trans
        (Eval.pointProjectorSelected
          (selected witness) (vector witness))
        (P729.sixTriplesAre729
          (vector witness (selected witness)))))
    (normalizerCancels729Amplitude witness)
projectionMatchesDelta witness x (Compare.differentX6 difference) =
  trans
    (cong (C3.multiply (normalizer witness))
      (Eval.pointProjectorOffPoint
        (selected witness) x (vector witness) difference))
    (trans
      (L.multiplyCommutative (normalizer witness) C3.zero)
      (L.zeroActsLeft (normalizer witness)))

normalisedProjectionIsDeltaPointwise :
  ∀ {Member inv}
    (witness : NonzeroInvariantVector {Member} inv) →
  V.PointwiseEqual
    (normalisedPointProjection witness)
    (comparisonDelta (selected witness))
normalisedProjectionIsDeltaPointwise witness x =
  projectionMatchesDelta witness x (Compare.compareX6 (selected witness) x)

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
