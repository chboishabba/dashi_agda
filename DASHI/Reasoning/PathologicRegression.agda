module DASHI.Reasoning.PathologicRegression where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Foundations.JPlusOneMarkedUnitExtension as JMarked
import DASHI.Foundations.MarkedUnitExtensionCore as Marked
import DASHI.Foundations.StageAtlasZeroToTwelve as Stage
import DASHI.Reasoning.PathologicConstraintSystem as Constraint
import DASHI.Reasoning.PathologicPerspectiveHyperfabric as Perspective
import DASHI.Reasoning.PathologicSourceAtlas as Sources
import DASHI.Reasoning.PathologicTheatreMetaRuntime as Theatre
import DASHI.Reasoning.RSITypedDependencyHyperfabric as RSI
import DASHI.Reasoning.TypedDependencyUpgradeAtlas as Upgrade

------------------------------------------------------------------------
-- Exact regression anchors for the typed-dependency and Pathologic tranche.
------------------------------------------------------------------------

stagePlusOneStillExact :
  JMarked.J-stage-carrier + 1 ≡ JMarked.J-stage-extended
stagePlusOneStillExact = JMarked.stageCarrierPlusOneExact

moonshinePlusOneStillExact :
  JMarked.J-moonshine-carrier + 1 ≡ JMarked.J-moonshine-extended
moonshinePlusOneStillExact = JMarked.moonshineCarrierPlusOneExact

dayTwoShockIsTenfold :
  Constraint.priceMultiplier Constraint.scarcityShock ≡ 10
dayTwoShockIsTenfold = Constraint.dayTwoPriceMultiplierIsTen

dayTwelveStageLensExact :
  Perspective.dayToStage Perspective.day-12
  ≡ Stage.stage-12
dayTwelveStageLensExact = Perspective.day12MapsToStage12

rsiRelationalNotTopological :
  RSI.RSITypedDependencyAuthorityBoundary.topologicalBorromeanLinkProved
    RSI.canonicalRSITypedDependencyAuthorityBoundary
  ≡ false
rsiRelationalNotTopological = refl

metaRevealRetainsTrace :
  Theatre.MetaReveal.traceAfterReveal Theatre.canonicalDeveloperMetaReveal
  ≡ Theatre.causalTraceRetained
metaRevealRetainsTrace = refl

hyphenIsCompoundLabel :
  JMarked.intendedJPreviousSubfibreReading
  ≡ JMarked.compoundSubfibreLabel
hyphenIsCompoundLabel = refl

freshUnitStillNotInternal :
  Marked.freshExternalUnit ≡ Marked.internalResidualUnit → ⊥
freshUnitStillNotInternal = Marked.freshExternalIsNotInternal

sourceAtlasCountIsTen :
  Source.sourceCount Sources.pathologicTypedDependencySources ≡ 10
sourceAtlasCountIsTen = refl

upgradeSiteCount : ∀ {A : Set} → List A → Nat
upgradeSiteCount [] = 0
upgradeSiteCount (_ ∷ rest) = 1 + upgradeSiteCount rest

dependencyUpgradeSiteCountIsSix :
  upgradeSiteCount Upgrade.canonicalDependencyUpgradeSites ≡ 6
dependencyUpgradeSiteCountIsSix = refl

noViewFromNowhereRegression : ¬ Perspective.ViewFromNowhere
noViewFromNowhereRegression = Perspective.noCanonicalViewFromNowhere
