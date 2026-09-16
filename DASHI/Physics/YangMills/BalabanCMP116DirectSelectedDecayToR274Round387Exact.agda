{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116DirectSelectedDecayToR274Round387Exact where

------------------------------------------------------------------------
-- ROUND387 / DIRECT SELECTED-J LOCALIZATION -> R274 CONNECTED TRAJECTORY
--
-- Post-#944 Pareto correction.
--
-- R386 showed that a fixed-point/Hessian DIFFERENCE estimate is not the
-- absolute selected localization consumed by canonical B.  Therefore do not
-- make the optional R384--R386 background-Hessian route a prerequisite for the
-- direct mass-gap producer.
--
-- R320 already isolates the least-privilege source-facing payment on the exact
-- selected finite-T5 carrier:
--
--   |D^2_{J_L,J_R} log Z| <= selected rooted connecting shell.
--
-- The normalized source calculus and R295/R341 identity make this exactly the
-- selected finite connected-covariance magnitude.  This owner performs only
-- that representation rewrite and constructs R274's connected-shell carrier.
-- No field-Hessian/source-cumulant identification is assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanCMP116TwoSourceConnectedClusteringRound274Exact as R274
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanT5DirectSelectedMarkedDecayRound320Exact as R320
import DASHI.Physics.YangMills.BalabanCMP116R281ModeSelectedDirectRound341Exact as R341
import DASHI.Physics.YangMills.BalabanUnifiedPolymerSchwingerNormExact as Unified

r320PaymentAsR274ConnectedShell :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension) →
  R320.DirectSelectedT5MarkedDecayPayment base →
  R274.TwoSourceConnectedRootedShellData
    (R318.Scale base) (R318.Volume base) (R318.Root base)
    Nat TestObservable
r320PaymentAsR274ConnectedShell
    {dataSet = dataSet} {extension = extension} base payment = record
  { R274.TwoSourceConnectedRootedShellData.shellData = R318.shellData base
  ; R274.TwoSourceConnectedRootedShellData.stateAtScale = λ cutoff → cutoff
  ; R274.TwoSourceConnectedRootedShellData.scaleOf = R318.scaleOf base
  ; R274.TwoSourceConnectedRootedShellData.volumeOf = R318.volumeOf base
  ; R274.TwoSourceConnectedRootedShellData.physicalDistance =
      R318.physicalDistance base
  ; R274.TwoSourceConnectedRootedShellData.connectingRoot =
      R318.connectingRoot base
  ; R274.TwoSourceConnectedRootedShellData.connectedCovarianceMagnitude =
      λ cutoff left right →
        R278.connectedCovarianceMagnitude extension
          (Gram.measureSequence dataSet cutoff) left right
  ; R274.TwoSourceConnectedRootedShellData.connectedCovarianceBelowConnectingShell =
      λ cutoff left right →
        subst
          (λ lower →
            lower ≤
              DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact.rootedShell
                (R318.shellData base)
                (R318.scaleOf base cutoff)
                (R318.volumeOf base cutoff)
                (R318.connectingRoot base cutoff left right)
                (R318.physicalDistance base left right))
          (R341.mixedLogMagnitudeIsFiniteSelectedCovarianceMagnitude
            base cutoff left right)
          (R320.literalSelectedJMagnitudeBelowShell
            payment cutoff left right)
  ; R274.TwoSourceConnectedRootedShellData.ConnectingClusterMeetsBothSupports =
      R318.ConnectingClusterMeetsBothSupports base
  }

r320PaymentBuildsQuantitativeCorrelationDecayTrajectory :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension) →
  R320.DirectSelectedT5MarkedDecayPayment base →
  Unified.QuantitativeCorrelationDecayTrajectory
r320PaymentBuildsQuantitativeCorrelationDecayTrajectory base payment =
  R274.asCorrelationDecayTrajectory
    (r320PaymentAsR274ConnectedShell base payment)

------------------------------------------------------------------------
-- Pareto / WrongType boundary.
------------------------------------------------------------------------

fieldHessianRouteMandatoryForDirectSelectedDecay : Bool
fieldHessianRouteMandatoryForDirectSelectedDecay = false

fieldHessianRouteMandatoryForDirectSelectedDecayIsFalse :
  fieldHessianRouteMandatoryForDirectSelectedDecay ≡ false
fieldHessianRouteMandatoryForDirectSelectedDecayIsFalse = refl

fieldHessianEqualsMixedSourceCumulantBySharedSecondDerivativeName : Bool
fieldHessianEqualsMixedSourceCumulantBySharedSecondDerivativeName = false

fieldHessianEqualsMixedSourceCumulantBySharedSecondDerivativeNameIsFalse :
  fieldHessianEqualsMixedSourceCumulantBySharedSecondDerivativeName ≡ false
fieldHessianEqualsMixedSourceCumulantBySharedSecondDerivativeNameIsFalse = refl

directSelectedDecayAlreadyProved : Bool
directSelectedDecayAlreadyProved = false

directSelectedDecayAlreadyProvedIsFalse :
  directSelectedDecayAlreadyProved ≡ false
directSelectedDecayAlreadyProvedIsFalse = refl

record Round387Boundary : Set where
  constructor round387-boundary
  field
    directSelectedJLocalizationIsSufficientFiniteProducer : Bool
    directSelectedJLocalizationIsSufficientFiniteProducerIsTrue :
      directSelectedJLocalizationIsSufficientFiniteProducer ≡ true

    r384ToR386ComparisonFamilyOptional : Bool
    r384ToR386ComparisonFamilyOptionalIsTrue :
      r384ToR386ComparisonFamilyOptional ≡ true

    backgroundFieldHessianAndSourceCumulantRemainDistinct : Bool
    backgroundFieldHessianAndSourceCumulantRemainDistinctIsTrue :
      backgroundFieldHessianAndSourceCumulantRemainDistinct ≡ true

canonicalRound387Boundary : Round387Boundary
canonicalRound387Boundary =
  round387-boundary true refl true refl true refl

round387DirectCompilerLevel : ProofLevel
round387DirectCompilerLevel = machineChecked

round387DirectSelectedLocalizationLevel : ProofLevel
round387DirectSelectedLocalizationLevel = R320.round320DirectSelectedMarkedDecayLevel

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
