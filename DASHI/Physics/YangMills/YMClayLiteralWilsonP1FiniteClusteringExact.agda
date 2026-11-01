{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLiteralWilsonP1FiniteClusteringExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; ∣_∣; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanT5DirectSelectedMarkedDecayRound320Exact as R320
import DASHI.Physics.YangMills.BalabanDirectR295ToR296MagnitudeCompilerRound313Exact as R313
import DASHI.Physics.YangMills.BalabanT5JMagnitudeDirectShellRound296Exact as R296
import DASHI.Physics.YangMills.BalabanCMP116DirectSelectedDecayToR274Round387Exact as R387
import DASHI.Physics.YangMills.BalabanCMP116TwoSourceConnectedClusteringRound274Exact as R274
import DASHI.Physics.YangMills.BalabanPairwiseEuclideanSemanticsRound310Exact as R310
import DASHI.Physics.YangMills.BalabanPairwiseWilsonBoundedTestsRound315Exact as R315
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power

------------------------------------------------------------------------
-- ROUTE-S P1 / FINITE INTERACTING LITERAL-WILSON CLUSTERING
--
-- This composes the existing source-localization theorem all the way to the
-- literal finite Wilson-pair statement consumed by Route S:
--
--   R320 selected mixed-log-source localization
--     -> R313 exact T5 magnitude presentation
--     -> R274 finite connected covariance <= (1/4)(1/2)^distance
--     -> selected Euclidean semantics distance = time.
--
-- No additional clustering estimate is introduced here.
------------------------------------------------------------------------

literalWilsonFiniteClustering :
  ∀ {Measure TestObservable PhysicalObservable Loop}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    (payment : R320.DirectSelectedT5MarkedDecayPayment base)
    (magnitudeIsAbsolute : ∀ value → R278.magnitude extension value ≡ ∣ value ∣)
    (semantics :
      R310.PairwiseEuclideanTimeSemantics
        {PhysicalObservable = PhysicalObservable}
        {dataSet = dataSet} {extension = extension}
        {finite =
          R313.exactT5JMagnitudeFromR295
            (R320.localizeBaseDirectlyAsR295 base payment)
            magnitudeIsAbsolute})
    (presentation :
      R315.PairwiseWilsonCylinderPresentation {Loop = Loop} semantics)
    (cutoff : Nat)
    (left right : PhysicalObservable)
    (time : Nat) →
  R278.connectedCovarianceMagnitude extension
    (Gram.measureSequence dataSet cutoff)
    (R310.decode semantics left)
    (R310.timeTranslate semantics right time)
  ≤ Shell.quarter * Power.rationalPower Geo.half time
literalWilsonFiniteClustering
    {dataSet = dataSet} {extension = extension}
    base payment magnitudeIsAbsolute semantics presentation
    cutoff left right time =
  let
    shell = R387.r320PaymentAsR274ConnectedShell base payment

    finiteBound =
      R274.connectedCovarianceGeometricBound shell cutoff
        (R310.decode semantics left)
        (R310.timeTranslate semantics right time)

    distanceIsTime :
      R274.physicalDistance shell
        (R310.decode semantics left)
        (R310.timeTranslate semantics right time)
      ≡ time
    distanceIsTime =
      R310.supportDistanceIsTime semantics left right time
  in
  subst
    (λ depth →
      R278.connectedCovarianceMagnitude extension
        (Gram.measureSequence dataSet cutoff)
        (R310.decode semantics left)
        (R310.timeTranslate semantics right time)
      ≤ Shell.quarter * Power.rationalPower Geo.half depth)
    distanceIsTime
    finiteBound

------------------------------------------------------------------------
-- P1 classification.
------------------------------------------------------------------------

newFiniteClusteringInequalityRequiredAfterR320 : Bool
newFiniteClusteringInequalityRequiredAfterR320 = false

newFiniteClusteringInequalityRequiredAfterR320IsFalse :
  newFiniteClusteringInequalityRequiredAfterR320 ≡ false
newFiniteClusteringInequalityRequiredAfterR320IsFalse = refl

selectedR320LocalizationStillPhysical : Bool
selectedR320LocalizationStillPhysical = true

selectedR320LocalizationStillPhysicalIsTrue :
  selectedR320LocalizationStillPhysical ≡ true
selectedR320LocalizationStillPhysicalIsTrue = refl

literalWilsonSameCarrierPresentationStillPhysical : Bool
literalWilsonSameCarrierPresentationStillPhysical = true

literalWilsonSameCarrierPresentationStillPhysicalIsTrue :
  literalWilsonSameCarrierPresentationStillPhysical ≡ true
literalWilsonSameCarrierPresentationStillPhysicalIsTrue = refl

p1FiniteLiteralWilsonClusteringCompilerLevel : ProofLevel
p1FiniteLiteralWilsonClusteringCompilerLevel = machineChecked

p1SelectedLocalizationLevel : ProofLevel
p1SelectedLocalizationLevel = R320.round320DirectSelectedMarkedDecayLevel

p1WilsonPresentationLevel : ProofLevel
p1WilsonPresentationLevel = R315.round315SelectedWilsonPresentationLevel

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
