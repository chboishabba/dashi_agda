{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanObservableIndexedT5SourceMeaningRound403Exact where

-- ROUND403 / REMOVE OBSERVABLE -> SOURCE-DIRECTION REPRESENTATION DEBT
--
-- `LiteralTwoSourceInsertionMeaning` does not require a separate syntactic J
-- carrier.  On the preferred selected-T5 route we can use the observable type
-- itself as the source-direction index and let the literal derivative maps be
-- exactly the already-owned normalized source-calculus maps.
--
-- This does NOT prove CMP116 localization.  It removes only the avoidable
-- post-hoc equality between a selected physical observable label and its J
-- direction.  The analytic theorem must still be instantiated on this literal
-- carrier.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ)

import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318

canonicalObservableIndexedMeaning :
  ∀ {Observable Scalar}
    {algebra : Cumulant.TwoSourceMomentAlgebra Observable Scalar} →
  (calculus : Cumulant.NormalizedLogSourceCalculus algebra) →
  Cumulant.LiteralTwoSourceInsertionMeaning calculus Observable
canonicalObservableIndexedMeaning calculus = record
  { Cumulant.LiteralTwoSourceInsertionMeaning.sourceDirectionOf = λ observable → observable
  ; Cumulant.LiteralTwoSourceInsertionMeaning.literalFirstDerivative =
      Cumulant.firstSourceDerivative calculus
  ; Cumulant.LiteralTwoSourceInsertionMeaning.literalMixedSecondDerivative =
      Cumulant.mixedSecondSourceDerivative calculus
  ; Cumulant.LiteralTwoSourceInsertionMeaning.literalMixedSecondLogDerivative =
      Cumulant.mixedSecondLogDerivative calculus
  ; Cumulant.LiteralTwoSourceInsertionMeaning.firstDirectionAgrees = λ observable → refl
  ; Cumulant.LiteralTwoSourceInsertionMeaning.secondDirectionAgrees = λ left right → refl
  ; Cumulant.LiteralTwoSourceInsertionMeaning.logSecondDirectionAgrees = λ left right → refl
  }

canonicalSourceDirectionIsObservable :
  ∀ {Observable Scalar}
    {algebra : Cumulant.TwoSourceMomentAlgebra Observable Scalar}
    (calculus : Cumulant.NormalizedLogSourceCalculus algebra)
    (observable : Observable) →
  Cumulant.sourceDirectionOf (canonicalObservableIndexedMeaning calculus) observable
  ≡ observable
canonicalSourceDirectionIsObservable calculus observable = refl

-- Preferred constructor for the R318 carrier.  All geometry remains supplied by
-- the selected physical T5 representation, but there is no extra SourceDirection
-- type or source-direction weld: it is definitionally `TestObservable`.
observableIndexedUnlocalizedT5 :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {Scale Volume Root : Set} →
  (calculus : Cumulant.NormalizedLogSourceCalculus
    (R318.R295.t5FiniteExpectationAlgebra dataSet extension)) →
  (shellData : Shell.TraversalShellData Scale Volume Root) →
  (scaleOf : Nat → Scale) →
  (volumeOf : Nat → Volume) →
  (physicalDistance : TestObservable → TestObservable → Nat) →
  (connectingRoot : Nat → TestObservable → TestObservable → Root) →
  (ConnectingClusterMeetsBothSupports :
    Nat → TestObservable → TestObservable → Set) →
  (signedBelowMagnitude : ∀ value → value R318.≤ R278.magnitude extension value) →
  R318.UnlocalizedT5StateFamilyJPresentation dataSet extension
observableIndexedUnlocalizedT5
    {Scale = Scale} {Volume = Volume} {Root = Root}
    calculus shellData scaleOf volumeOf physicalDistance connectingRoot
    ConnectingClusterMeetsBothSupports signedBelowMagnitude = record
  { R318.UnlocalizedT5StateFamilyJPresentation.Scale = Scale
  ; R318.UnlocalizedT5StateFamilyJPresentation.Volume = Volume
  ; R318.UnlocalizedT5StateFamilyJPresentation.Root = Root
  ; R318.UnlocalizedT5StateFamilyJPresentation.SourceDirection = _
  ; R318.UnlocalizedT5StateFamilyJPresentation.calculus = calculus
  ; R318.UnlocalizedT5StateFamilyJPresentation.meaning =
      canonicalObservableIndexedMeaning calculus
  ; R318.UnlocalizedT5StateFamilyJPresentation.shellData = shellData
  ; R318.UnlocalizedT5StateFamilyJPresentation.scaleOf = scaleOf
  ; R318.UnlocalizedT5StateFamilyJPresentation.volumeOf = volumeOf
  ; R318.UnlocalizedT5StateFamilyJPresentation.physicalDistance = physicalDistance
  ; R318.UnlocalizedT5StateFamilyJPresentation.connectingRoot = connectingRoot
  ; R318.UnlocalizedT5StateFamilyJPresentation.ConnectingClusterMeetsBothSupports =
      ConnectingClusterMeetsBothSupports
  ; R318.UnlocalizedT5StateFamilyJPresentation.signedBelowMagnitude =
      signedBelowMagnitude
  }
