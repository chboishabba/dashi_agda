module DASHI.Physics.Gravity.IntrinsicPenroseInterpretationRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Gravity.IntrinsicSpacetimeCurvatureInterpretationExact as Intrinsic
import DASHI.Physics.Gravity.Penrose1965NullGeodesicIncompletenessExact as Penrose

rubberSheetFirewallRegression :
  Intrinsic.rubberSheetEmbeddingIsNotIntrinsicLorentzianCurvature
    Intrinsic.canonicalIntrinsicCurvatureInterpretationBoundary
  ≡ true
rubberSheetFirewallRegression = refl

temporalPhraseFirewallRegression :
  Intrinsic.timeCurvesIntoSpacePhraseIsNotInvariantGRStatement
    Intrinsic.canonicalIntrinsicCurvatureInterpretationBoundary
  ≡ true
temporalPhraseFirewallRegression = refl

incompletenessPointFirewallRegression :
  Penrose.geodesicIncompletenessIsNotSingularPointInSpacetime
    Penrose.canonicalPenroseInterpretationBoundary
  ≡ true
incompletenessPointFirewallRegression = refl

curvatureDivergenceFirewallRegression :
  Penrose.incompletenessDoesNotRequireCurvatureScalarDivergence
    Penrose.canonicalPenroseInterpretationBoundary
  ≡ true
curvatureDivergenceFirewallRegression = refl

continuumPromotionStillClosedRegression :
  Penrose.penroseOwnerPromotesContinuumGR ≡ false
continuumPromotionStillClosedRegression = refl
