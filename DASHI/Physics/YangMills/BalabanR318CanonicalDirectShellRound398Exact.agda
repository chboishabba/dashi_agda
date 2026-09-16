{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanR318CanonicalDirectShellRound398Exact where

------------------------------------------------------------------------
-- ROUND398 / BUILD THE R284 DIRECT SHELL FROM THE R318 SELECTED CARRIER
--
-- Historical R304/R349 allowed an independently supplied R284 direct shell and
-- then charged a same-object equality between its distance and R318's physical
-- distance.  That equality is avoidable when the direct shell is constructed
-- from the selected carrier itself.
--
-- Input:
--   * the exact R318 unlocalized selected T5 carrier;
--   * the one R320 physical/source theorem on that carrier.
--
-- Output:
--   * an R284 DirectT5TwoSourceShell whose shell data, cutoff scale/volume,
--     physical distance, connecting root and support-connectivity predicate are
--     definitionally inherited from R318.
--
-- The only non-structural field is the already-paid R320 connected-shell bound;
-- mixed-log -> finite covariance magnitude is compiler-owned by R295.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanT5DirectSelectedMarkedDecayRound320Exact as R320
import DASHI.Physics.YangMills.BalabanT5StateFamilySourceAlgebraRound295Exact as R295
import DASHI.Physics.YangMills.BalabanCMP116DirectT5ContinuumClusteringRound284Exact as R284
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell

canonicalDirectShell :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension) →
  R320.DirectSelectedT5MarkedDecayPayment base →
  R284.DirectT5TwoSourceShell dataSet extension
canonicalDirectShell {dataSet = dataSet} {extension = extension} base payment =
  let
    localized = R320.localizeBaseDirectlyAsR295 base payment
  in
  record
    { R284.DirectT5TwoSourceShell.Scale = R318.Scale base
    ; R284.DirectT5TwoSourceShell.Volume = R318.Volume base
    ; R284.DirectT5TwoSourceShell.Root = R318.Root base
    ; R284.DirectT5TwoSourceShell.shellData = R318.shellData base
    ; R284.DirectT5TwoSourceShell.scaleAtCutoff = R318.scaleOf base
    ; R284.DirectT5TwoSourceShell.volumeAtCutoff = R318.volumeOf base
    ; R284.DirectT5TwoSourceShell.physicalDistance = R318.physicalDistance base
    ; R284.DirectT5TwoSourceShell.connectingRoot = R318.connectingRoot base
    ; R284.DirectT5TwoSourceShell.finiteCovarianceBelowConnectingShell =
        λ cutoff left right →
          let
            literalBound = R320.literalSelectedJMagnitudeBelowShell
              payment cutoff left right
            equality = R295.mixedLogMagnitudeIsExactFiniteT5CovarianceMagnitude
              localized cutoff left right
          in
          subst
            (λ lower →
              lower ≤ Shell.rootedShell (R318.shellData base)
                (R318.scaleOf base cutoff)
                (R318.volumeOf base cutoff)
                (R318.connectingRoot base cutoff left right)
                (R318.physicalDistance base left right))
            equality
            literalBound
    ; R284.DirectT5TwoSourceShell.connectingClusterMeetsBothSupports =
        R318.ConnectingClusterMeetsBothSupports base
    }

canonicalDirectShellDistanceIsR318 :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    (payment : R320.DirectSelectedT5MarkedDecayPayment base)
    left right →
  R284.physicalDistance (canonicalDirectShell base payment) left right
  ≡ R318.physicalDistance base left right
canonicalDirectShellDistanceIsR318 base payment left right = refl

canonicalDirectShellRootIsR318 :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    (payment : R320.DirectSelectedT5MarkedDecayPayment base)
    cutoff left right →
  R284.connectingRoot (canonicalDirectShell base payment) cutoff left right
  ≡ R318.connectingRoot base cutoff left right
canonicalDirectShellRootIsR318 base payment cutoff left right = refl

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

round398CanonicalDirectShellCompilerLevel : ProofLevel
round398CanonicalDirectShellCompilerLevel = machineChecked

independentR284DistanceCarrierRequired : Bool
independentR284DistanceCarrierRequired = false

independentR284DistanceCarrierRequiredIsFalse :
  independentR284DistanceCarrierRequired ≡ false
independentR284DistanceCarrierRequiredIsFalse = refl

r349CrossCarrierDistanceWeldRequiredOnCanonicalConstruction : Bool
r349CrossCarrierDistanceWeldRequiredOnCanonicalConstruction = false

r349CrossCarrierDistanceWeldRequiredOnCanonicalConstructionIsFalse :
  r349CrossCarrierDistanceWeldRequiredOnCanonicalConstruction ≡ false
r349CrossCarrierDistanceWeldRequiredOnCanonicalConstructionIsFalse = refl

selectedPhysicalDistanceTimeSemanticsStillProofBearing : Bool
selectedPhysicalDistanceTimeSemanticsStillProofBearing = true

selectedPhysicalDistanceTimeSemanticsStillProofBearingIsTrue :
  selectedPhysicalDistanceTimeSemanticsStillProofBearing ≡ true
selectedPhysicalDistanceTimeSemanticsStillProofBearingIsTrue = refl

freshYMDecayEstimateIntroduced : Bool
freshYMDecayEstimateIntroduced = false

freshYMDecayEstimateIntroducedIsFalse :
  freshYMDecayEstimateIntroduced ≡ false
freshYMDecayEstimateIntroducedIsFalse = refl

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
