module DASHI.Physics.Gravity.IntrinsicPenroseInterpretationRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Gravity.IntrinsicSpacetimeCurvatureInterpretationExact as Intrinsic
import DASHI.Physics.Gravity.CausalFutureHorismosNullGeneratorExact as Causal
import DASHI.Physics.Gravity.NullRaychaudhuriSachsFocusingExact as Focusing
import DASHI.Physics.Gravity.PenroseHorismosCompactnessPaymentExact as Compactness
import DASHI.Physics.Gravity.PenroseGlobalCausalityAuthorityExact as Authority
import DASHI.Physics.Gravity.PenroseGlobalHorismosContradictionExact as Global
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

causalVsChronologicalFutureFirewallRegression :
  Causal.causalFutureIsNotChronologicalFuture
    Causal.canonicalCausalFutureInterpretationBoundary ≡ true
causalVsChronologicalFutureFirewallRegression = refl

horismosNotEventHorizonRegression :
  Causal.horismosIsNotEventHorizon
    Causal.canonicalCausalFutureInterpretationBoundary ≡ true
horismosNotEventHorizonRegression = refl

causalBoundaryDerivationStillClosedRegression :
  Causal.causalBoundaryOwnerInternallyReprovesContinuumCausality
    Causal.canonicalCausalFutureHorismosBoundary ≡ false
causalBoundaryDerivationStillClosedRegression = refl

localFocusingNotGlobalIncompletenessRegression :
  Focusing.localFocusingDoesNotEqualGlobalGeodesicIncompleteness
    Focusing.canonicalNullFocusingCompositionBoundary
  ≡ true
localFocusingNotGlobalIncompletenessRegression = refl

energyConditionTranslationFirewallRegression :
  Focusing.nullEnergyConditionIsNotNullConvergenceWithoutEinsteinEquation
    Focusing.canonicalNullFocusingCompositionBoundary
  ≡ true
energyConditionTranslationFirewallRegression = refl

focusingContinuumDerivationStillClosedRegression :
  Focusing.focusingOwnerInternallyDerivesContinuumEquation
    Focusing.canonicalNullOpticalFocusingBoundary
  ≡ false
focusingContinuumDerivationStillClosedRegression = refl

pointwiseNegativeNotUniformRegression :
  Compactness.pointwiseNegativeExpansionDoesNotAloneGiveUniformBound
    Compactness.canonicalPenroseCompactnessInterpretationBoundary ≡ true
pointwiseNegativeNotUniformRegression = refl

rawNullVectorFibreFirewallRegression :
  Compactness.rawNullNormalVectorFibreIsNotCompactDirectionFibre
    Compactness.canonicalPenroseCompactnessInterpretationBoundary ≡ true
rawNullVectorFibreFirewallRegression = refl

boundedParameterNotCompactnessRegression :
  Compactness.boundedAffineParameterDoesNotAloneMakeHorismosCompact
    Compactness.canonicalPenroseCompactnessInterpretationBoundary ≡ true
boundedParameterNotCompactnessRegression = refl

compactnessTopologyDerivationStillClosedRegression :
  Compactness.compactnessOwnerInternallyReprovesContinuumTopology
    Compactness.canonicalPenroseHorismosCompactnessBoundary ≡ false
compactnessTopologyDerivationStillClosedRegression = refl

globalAuthorityCitationNonPromotionRegression :
  Authority.authorityCitationImportsNeitherProofNorAuthority
    Authority.canonicalGlobalCausalityAuthorityReceipt ≡ true
globalAuthorityCitationNonPromotionRegression = refl

globalAuthorityDerivationStillClosedRegression :
  Authority.authorityOwnerInternallyReprovesGlobalCausality
    Authority.canonicalGlobalCausalityAuthorityReceipt ≡ false
globalAuthorityDerivationStillClosedRegression = refl

compactHorismosNotSingularityRegression :
  Global.compactHorismosIsNotSpacetimeSingularity
    Global.canonicalPenroseGlobalInterpretationBoundary
  ≡ true
compactHorismosNotSingularityRegression = refl

nonCompactCauchyIsGlobalInputRegression :
  Global.nonCompactCauchyIsTopologicalGlobalInputNotLocalCurvature
    Global.canonicalPenroseGlobalInterpretationBoundary
  ≡ true
nonCompactCauchyIsGlobalInputRegression = refl

globalCausalityDerivationStillClosedRegression :
  Global.globalOwnerInternallyReprovesContinuumCausality
    Global.canonicalPenroseGlobalHorismosBoundary
  ≡ false
globalCausalityDerivationStillClosedRegression = refl

continuumPromotionStillClosedRegression :
  Penrose.penroseOwnerPromotesContinuumGR ≡ false
continuumPromotionStillClosedRegression = refl
