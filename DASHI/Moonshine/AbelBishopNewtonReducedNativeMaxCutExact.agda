module DASHI.Moonshine.AbelBishopNewtonReducedNativeMaxCutExact where

------------------------------------------------------------------------
-- REDUCED EXACT PHYSICAL/ANALYTIC NEWTON MAX-CUT.
--
-- The Bishop Newton source no longer requires callers to furnish:
--  * a sine positivity / reciprocal witness,
--  * an arbitrary first-step estimate,
--  * an arbitrary disk self-map proof,
--  * an arbitrary Newton-endomap continuity proof.
--
-- Actual original sine source fills the reciprocal.
-- Actual ORIGINAL expC(c)-c and expC(c)-1 Taylor inequalities fill
-- the first-step estimate.  Squared contraction + the constructive
-- two-norm parallelogram bound fills disk self-map.
-- Three scalar exp/sin/cos limits fill Newton-endomap continuity.
--
-- Two genuinely analytic source obligations remain:
--  (1) Bishop-native numeric Taylor bounds and uniform squared
--      Newton contraction on the selected radius-1/200 disk;
--  (2) convergence of the genuine original scalar exp/cos/sin
--      values along the same completed Newton trajectory.
--
-- Everything here is source written, not independently kernel checked.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexReciprocalExact as Reciprocal
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian

import DASHI.Moonshine.AbelBishopOriginalComplexCarrierWeldExact as Native
import DASHI.Moonshine.AbelBishopNewtonSelectedOperatorExact as Newton
import DASHI.Moonshine.AbelBishopNewtonSelectedSinePositiveExact as Sine
import DASHI.Moonshine.AbelBishopNewtonSelectedLimitExact as Limit
import DASHI.Moonshine.AbelBishopAnalyticNewtonContractionExact as Disk
import DASHI.Moonshine.AbelBishopNewtonLiteralFirstStepFromTaylorExact as Taylor
import DASHI.Moonshine.AbelBishopNewtonDiskSelfMapFromSquareContractionExact as SelfMap
import DASHI.Moonshine.AbelBishopNewtonSourceInhabitationExact as Source
import DASHI.Moonshine.AbelBishopKoenigsSelectedRationalConstantsExact as Constants

selectedNewtonNonzero :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  Reciprocal.BishopComplexNonzero
    (Newton.originalBishopNewtonDenominator T)
selectedNewtonNonzero =
  Sine.originalBishopNewtonDenominatorNonzeroFromSource

OriginalBishopNativeSquaredContraction :
  (T : Cartesian.BishopSetoidComplexTranscendentals) → Set
OriginalBishopNativeSquaredContraction T =
  let nz = selectedNewtonNonzero T in
  ∀ z w →
  Disk.originalBishopSelectedNewtonDisk z →
  Disk.originalBishopSelectedNewtonDisk w →
  BishopReal._≤_
    (Disk.originalBishopSquaredDistance
      (Newton.originalBishopNewtonOperator T nz z)
      (Newton.originalBishopNewtonOperator T nz w))
    (BishopReal._*_
      (Norm.square
        Constants.bishopSelectedNewtonRatio)
      (Disk.originalBishopSquaredDistance z w))

selectedReducedDiskCertificate :
  ∀ T →
  Taylor.OriginalBishopNewtonLiteralTaylorCenterBounds T →
  OriginalBishopNativeSquaredContraction T →
  Disk.OriginalBishopAnalyticNewtonContraction
    T (selectedNewtonNonzero T)
selectedReducedDiskCertificate T center contractive =
  SelfMap.originalBishopNewtonContractionFromLiteralTaylorAndSquare
    T (selectedNewtonNonzero T) contractive center

selectedReducedNewtonSteps :
  ∀ T →
  (center : Taylor.OriginalBishopNewtonLiteralTaylorCenterBounds T) →
  (contractive : OriginalBishopNativeSquaredContraction T) →
  Limit.OriginalBishopNewtonSelectedStepBounds
    T (selectedNewtonNonzero T)
selectedReducedNewtonSteps T center contractive =
  Disk.originalBishopAnalyticNewtonBuildsActualStepBounds
    T (selectedNewtonNonzero T)
    (selectedReducedDiskCertificate T center contractive)

selectedReducedNewtonPoint :
  ∀ T →
  (center : Taylor.OriginalBishopNewtonLiteralTaylorCenterBounds T) →
  (contractive : OriginalBishopNativeSquaredContraction T) →
  Complex.BishopComplex
selectedReducedNewtonPoint T center contractive =
  Limit.originalBishopSelectedNewtonLimit
    T (selectedNewtonNonzero T)
    (selectedReducedNewtonSteps T center contractive)

record OriginalBishopReducedNewtonAnalyticInputs
    (T : Cartesian.BishopSetoidComplexTranscendentals) : Set₁ where
  field
    nativeTaylorAtCenter :
      Taylor.OriginalBishopNewtonLiteralTaylorCenterBounds T

    nativeSquaredContraction :
      OriginalBishopNativeSquaredContraction T

  private
    nz = selectedNewtonNonzero T
    center = nativeTaylorAtCenter
    contractive = nativeSquaredContraction
    orbit = Newton.originalBishopNewtonOrbit T nz
    point = selectedReducedNewtonPoint T center contractive

  field
    nativeExpAlongNewton :
      BishopSequence._ConvergesTo_
        (λ n → Exp.bishopExp (Complex.re (orbit n)))
        (Exp.bishopExp (Complex.re point))

    nativeCosAlongNewton :
      BishopSequence._ConvergesTo_
        (λ n → Elementary.bishopCos
          (Cartesian.dataSet T) (Complex.im (orbit n)))
        (Elementary.bishopCos
          (Cartesian.dataSet T) (Complex.im point))

    nativeSinAlongNewton :
      BishopSequence._ConvergesTo_
        (λ n → Elementary.bishopSin
          (Cartesian.dataSet T) (Complex.im (orbit n)))
        (Elementary.bishopSin
          (Cartesian.dataSet T) (Complex.im point))

open OriginalBishopReducedNewtonAnalyticInputs public

originalReducedNewtonBuildsOriginalSource :
  ∀ T →
  OriginalBishopReducedNewtonAnalyticInputs T →
  Source.OriginalBishopNewtonActualAnalyticSources T
originalReducedNewtonBuildsOriginalSource T source =
  record
    { Source.selectedDiskCertificate =
        selectedReducedDiskCertificate T
          (nativeTaylorAtCenter source)
          (nativeSquaredContraction source)
    ; Source.originalExpContinuousAlongNewton =
        nativeExpAlongNewton source
    ; Source.originalCosContinuousAlongNewton =
        nativeCosAlongNewton source
    ; Source.originalSinContinuousAlongNewton =
        nativeSinAlongNewton source
    }

originalReducedNewtonGivesActualNativeExpFixed :
  ∀ T →
  (source : OriginalBishopReducedNewtonAnalyticInputs T) →
  Complex._≈C_
    (Native.originalBishopExpOnSeries T
      (Source.originalBishopSelectedNewtonFixedPoint T
        (originalReducedNewtonBuildsOriginalSource T source)))
    (Source.originalBishopSelectedNewtonFixedPoint T
      (originalReducedNewtonBuildsOriginalSource T source))
originalReducedNewtonGivesActualNativeExpFixed T source =
  Source.originalBishopSelectedNewtonFixedPointIsExpFixed
    T (originalReducedNewtonBuildsOriginalSource T source)
