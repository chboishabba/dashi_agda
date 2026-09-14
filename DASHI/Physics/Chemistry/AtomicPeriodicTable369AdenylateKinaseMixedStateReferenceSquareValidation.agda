module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseMixedStateReferenceSquareValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseMixedStateReferenceSquareExact as S

------------------------------------------------------------------------
-- RED/GREEN validation root for the four-corner AdK structural reference set.
-- The critical regression is not merely that four labels exist: carrier
-- heterogeneity must remain explicit so the cross-homolog square cannot be
-- promoted to same-sequence domain-independence evidence.
------------------------------------------------------------------------

cornerRegression :
  S.MixedStateReferenceBoundary.fourStructuralCornersRepresented
    S.canonicalMixedStateReferenceBoundary
  ≡ true
  × S.MixedStateReferenceBoundary.mixedCornersSourcePaid
    S.canonicalMixedStateReferenceBoundary
  ≡ true
cornerRegression = refl , refl

carrierRegression :
  S.MixedStateReferenceBoundary.allFourCornersShareSameProteinSequence
    S.canonicalMixedStateReferenceBoundary
  ≡ false
  × S.MixedStateReferenceBoundary.crossHomologSquareProvesSameSequenceAxisIndependence
    S.canonicalMixedStateReferenceBoundary
  ≡ false
carrierRegression = refl , refl

promotionRegression :
  S.MixedStateReferenceBoundary.referenceSquareUsefulForCoordinateHypothesis
    S.canonicalMixedStateReferenceBoundary
  ≡ true
  × S.MixedStateReferenceBoundary.referenceSquareProvesUniversalMechanism
    S.canonicalMixedStateReferenceBoundary
  ≡ false
promotionRegression = refl , refl
