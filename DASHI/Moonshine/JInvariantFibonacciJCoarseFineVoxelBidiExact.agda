module DASHI.Moonshine.JInvariantFibonacciJCoarseFineVoxelBidiExact where

------------------------------------------------------------------------
-- FIBONACCI 9/27 <-> jCOARSE/jFINE LOCAL-VOXEL BIDI
--
-- Existing owners already prove:
--
--   jCoarse ordinary carrier  <-> PhaseQuotient9 = C3 x C3
--   jFine                     <-> (PhaseQuotient9 -> C3)
--
-- Hence one structured absolute j state is a chosen coarse point q together
-- with a complete ternary field f over the nine coarse points.  Evaluation at
-- the chosen point gives the local 27-state observer
--
--   (q , f) |-> (q_1 , q_2 , f q).
--
-- This map has an exact section: choose q=(a,b) and the constant field c.
-- Thus the repo's local 27 voxel is an observer of the richer jCoarse/jFine
-- fibre, not a cardinality coincidence and not the whole 3^11 carrier.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.JFineCoarseRelativeScaleExact as Scale
import DASHI.Biology.JFinePhaseQuotientFieldExact as Fine
import DASHI.Biology.TernaryPhaseQuotientJCoarseBridgeExact as Coarse
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Foundations.TernaryEndomorphismPhaseQuotientExact as Phase
import DASHI.Moonshine.GoldenRatioFibonacci369SheetVoxelBridgeExact as Fib
import DASHI.Moonshine.JInvariantOrderThreeOrbitBalancedTernaryBidiExact as Orbit

kernelToBase : Triadic.KernelTrit -> Base.TriTruth
kernelToBase Triadic.negativeTrit = Base.tri-low
kernelToBase Triadic.zeroTrit = Base.tri-mid
kernelToBase Triadic.positiveTrit = Base.tri-high

baseToKernel : Base.TriTruth -> Triadic.KernelTrit
baseToKernel Base.tri-low = Triadic.negativeTrit
baseToKernel Base.tri-mid = Triadic.zeroTrit
baseToKernel Base.tri-high = Triadic.positiveTrit

baseAfterKernel :
  (t : Triadic.KernelTrit) -> baseToKernel (kernelToBase t) ≡ t
baseAfterKernel Triadic.negativeTrit = refl
baseAfterKernel Triadic.zeroTrit = refl
baseAfterKernel Triadic.positiveTrit = refl

kernelAfterBase :
  (t : Base.TriTruth) -> kernelToBase (baseToKernel t) ≡ t
kernelAfterBase Base.tri-low = refl
kernelAfterBase Base.tri-mid = refl
kernelAfterBase Base.tri-high = refl

nineToPhase : Triadic.NineSheet -> Phase.PhaseQuotient9
nineToPhase (left , right) = kernelToBase left , kernelToBase right

phaseToNine : Phase.PhaseQuotient9 -> Triadic.NineSheet
phaseToNine (left , right) = baseToKernel left , baseToKernel right

phaseAfterNine :
  (sheet : Triadic.NineSheet) -> phaseToNine (nineToPhase sheet) ≡ sheet
phaseAfterNine (left , right)
  rewrite baseAfterKernel left | baseAfterKernel right = refl

nineAfterPhase :
  (sheet : Phase.PhaseQuotient9) -> nineToPhase (phaseToNine sheet) ≡ sheet
nineAfterPhase (left , right)
  rewrite kernelAfterBase left | kernelAfterBase right = refl

fibComparisonPhase : Fib.DefectLine3 -> Phase.PhaseQuotient9
fibComparisonPhase t = nineToPhase (Fib.fibComparison t)

fibComparisonJCoarse : Fib.DefectLine3 -> Harmonic.CoarseChannel
fibComparisonJCoarse t =
  Coarse.phaseQuotientToOrdinaryCoarse (fibComparisonPhase t)

fibNegativeJCoarse :
  fibComparisonJCoarse Triadic.negativeTrit
  ≡ Harmonic.ordinaryChannel
      (Harmonic.balancedPair Harmonic.negativeTrit Harmonic.positiveTrit)
fibNegativeJCoarse = refl

fibCentreJCoarse :
  fibComparisonJCoarse Triadic.zeroTrit
  ≡ Harmonic.ordinaryChannel
      (Harmonic.balancedPair Harmonic.zeroTrit Harmonic.zeroTrit)
fibCentreJCoarse = refl

fibPositiveJCoarse :
  fibComparisonJCoarse Triadic.positiveTrit
  ≡ Harmonic.ordinaryChannel
      (Harmonic.balancedPair Harmonic.positiveTrit Harmonic.negativeTrit)
fibPositiveJCoarse = refl

StructuredJAbsolute : Set
StructuredJAbsolute = Phase.PhaseQuotient9 × Harmonic.FineFrequency

LocalPhaseVoxel27 : Set
LocalPhaseVoxel27 = Phase.PhaseQuotient9 × Base.TriTruth

structuredCoarse : StructuredJAbsolute -> Phase.PhaseQuotient9
structuredCoarse (coarse , fine) = coarse

structuredFine : StructuredJAbsolute -> Harmonic.FineFrequency
structuredFine (coarse , fine) = fine

localVoxelObserver : StructuredJAbsolute -> LocalPhaseVoxel27
localVoxelObserver (coarse , fine) =
  coarse , Fine.decodePhaseFineField fine coarse

constantPhaseFineField : Base.TriTruth -> Fine.PhaseFineField
constantPhaseFineField value coarse = value

localVoxelSection : LocalPhaseVoxel27 -> StructuredJAbsolute
localVoxelSection (coarse , value) =
  coarse , Fine.encodePhaseFineField (constantPhaseFineField value)

localVoxelAfterSection :
  (voxel : LocalPhaseVoxel27) ->
  localVoxelObserver (localVoxelSection voxel) ≡ voxel
localVoxelAfterSection (coarse , value)
  rewrite Fine.decodeAfterEncodePhaseFinePointwise
    (constantPhaseFineField value) coarse = refl

phaseLocalToFibVoxel : LocalPhaseVoxel27 -> Fib.FibVoxel27
phaseLocalToFibVoxel ((a , b) , c) =
  baseToKernel a , baseToKernel b , baseToKernel c

fibVoxelToPhaseLocal : Fib.FibVoxel27 -> LocalPhaseVoxel27
fibVoxelToPhaseLocal (a , b , c) =
  (kernelToBase a , kernelToBase b) , kernelToBase c

fibAfterPhaseLocal :
  (voxel : LocalPhaseVoxel27) ->
  fibVoxelToPhaseLocal (phaseLocalToFibVoxel voxel) ≡ voxel
fibAfterPhaseLocal ((a , b) , c)
  rewrite kernelAfterBase a | kernelAfterBase b | kernelAfterBase c = refl

phaseAfterFibVoxel :
  (voxel : Fib.FibVoxel27) ->
  phaseLocalToFibVoxel (fibVoxelToPhaseLocal voxel) ≡ voxel
phaseAfterFibVoxel (a , b , c)
  rewrite baseAfterKernel a | baseAfterKernel b | baseAfterKernel c = refl

fibFineField : Fib.DefectLine3 -> Fine.PhaseFineField
fibFineField t = constantPhaseFineField (kernelToBase t)

fibStructuredJAbsolute : Fib.DefectLine3 -> StructuredJAbsolute
fibStructuredJAbsolute t =
  fibComparisonPhase t , Fine.encodePhaseFineField (fibFineField t)

fibStructuredProjectsToFibVoxel :
  (t : Fib.DefectLine3) ->
  phaseLocalToFibVoxel
    (localVoxelObserver (fibStructuredJAbsolute t))
  ≡ Fib.fibVoxel t
fibStructuredProjectsToFibVoxel Triadic.negativeTrit = refl
fibStructuredProjectsToFibVoxel Triadic.zeroTrit = refl
fibStructuredProjectsToFibVoxel Triadic.positiveTrit = refl

jCoarseIsNine : Scale.jCoarseFrequency ≡ 9
jCoarseIsNine = refl

jFineIsThreePowerNine : Scale.jFineFrequency ≡ 19683
jFineIsThreePowerNine = refl

jAbsoluteIsThreePowerEleven : Scale.jAbsoluteFineFrequency ≡ 177147
jAbsoluteIsThreePowerEleven = refl

jAbsoluteFactorsAsCoarseTimesFine :
  Scale.jAbsoluteFineFrequency ≡ Scale.jCoarseFrequency * Scale.jFineFrequency
jAbsoluteFactorsAsCoarseTimesFine = Scale.jAbsoluteFineIsCoarseTimesJFine

record JCoarseFineSeamRecognizer : Set₁ where
  field
    recogniseIndex : StructuredJAbsolute -> Nat
    recognisedScale : StructuredJAbsolute -> Nat
    scaleLaw :
      (state : StructuredJAbsolute) ->
      recognisedScale state ≡ Orbit.orbitNorm (recogniseIndex state)

data JCoarseFineVoxelResidual : Set where
  missingRenderedSeamToStructuredJAbsolute : JCoarseFineVoxelResidual
  missingStructuredJAbsoluteToOrbitIndexRecognizer : JCoarseFineVoxelResidual
  missingFineSensitiveGluingTransport : JCoarseFineVoxelResidual
  missingMonsterGradeWiseAbsoluteFieldIntertwiner : JCoarseFineVoxelResidual

record JCoarseFineVoxelFrontier : Set where
  constructor j-coarse-fine-voxel-frontier
  field
    fibNineSheetEqualsOrdinaryJCoarseCarrier : Bool
    structuredJFineFieldCodecExact : Bool
    localTwentySevenObserverExact : Bool
    localTwentySevenObserverHasSection : Bool
    fibonacciVoxelHasStructuredJAbsoluteSection : Bool
    absoluteScaleThreePowerElevenExact : Bool
    renderedSeamAcquiredAsStructuredJAbsolute : Bool
    orbitIndexRecognisedFromStructuredJAbsolute : Bool
    firstResidual : JCoarseFineVoxelResidual

canonicalJCoarseFineVoxelFrontier : JCoarseFineVoxelFrontier
canonicalJCoarseFineVoxelFrontier =
  j-coarse-fine-voxel-frontier
    true true true true true true false false
    missingRenderedSeamToStructuredJAbsolute
