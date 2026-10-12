{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityDirectSourceVacuumStressExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (_*_)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Closure.SymbolicEinsteinHilbertModel as EH
import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Stress
import DASHI.Physics.Foundations.GRQFTVacuumStressLambdaCompilerExact as VacuumStress
import DASHI.Physics.Foundations.CMP119AntigravityLocalizedVacuumReadoutExact as Readout
import DASHI.Physics.Foundations.CMP119AntigravityVacuumNormalizationGravityFirewallExact as Firewall
import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as Source
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4

------------------------------------------------------------------------
-- SOURCE VACUUM CONSTANT COORDINATE -> CANDIDATE COSMOLOGICAL-STRESS SHAPE
--
-- The scalar used below is the LocalizedAction constant/remainder coordinate,
-- not the plaquette coefficient.  The tensor algebra is exact: any scalar can
-- be placed on the already-owned vacuum-stress ray T = -lambda g.
--
-- This remains a CANDIDATE shape until two distinct semantic payments are made:
--
--   1. published CMP119 vacuumEnergy is encoded as the selected pure constant
--      action / normalization coordinate;
--   2. the same renormalized effective action has the required metric response
--      under an explicit cosmological renormalization convention/calibration.
------------------------------------------------------------------------

symbolicVacuumVariationShape :
  EH.varyInvariant EH.vacuumDensity ≡ EH.cosmologicalTensorTerm
symbolicVacuumVariationShape = EH.vacuumVariationIsCosmological

module _
  {Density Background Fluctuation : Set}
  (source : Source.CMP119Section2SourceNativeState
    Density Background Fluctuation
    T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
    T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction)
  where

  sourceVacuumStressAtScale : Nat → Stress.RationalTensor4
  sourceVacuumStressAtScale scale =
    VacuumStress.vacuumStressAt
      (Readout.localizedVacuumValue source scale)

  sourceVacuumStressAtScaleIsCandidateShape : Bool
  sourceVacuumStressAtScaleIsCandidateShape = true

  sourceVacuumStressIsMinusLambdaMetric :
    ∀ scale (a b : Flat.Axis4) →
    sourceVacuumStressAtScale scale a b
    ≡ Readout.localizedVacuumValue source scale
        * VacuumStress.negativeMetric a b
  sourceVacuumStressIsMinusLambdaMetric scale a b =
    VacuumStress.vacuumStressIsMinusLambdaMetric
      (Readout.localizedVacuumValue source scale) a b

record DirectSourceVacuumStressBoundary : Set where
  constructor direct-source-vacuum-stress-boundary
  field
    constantRemainderCoordinateUsed : Bool
    plaquetteProjectorUsedAsVacuumConstant : Bool
    publishedVacuumConstantEncodingRequired : Bool
    actualSourceVacuumCoefficientFeedsStressDirectly : Bool
    symbolicVacuumVariationShapeAlreadyOwned : Bool
    algebraicCandidateVacuumStressShapeOwned : Bool
    metricVolumeSameObjectReceiptRequiredForPhysicalPromotion : Bool
    cosmologicalRenormalizationReceiptRequiredForPhysicalPromotion : Bool
    fixedAmplitudeReceiptRequired : Bool
    pinnedNormalizedStressTensorRequired : Bool
    independentCosmologicalStressShapeRequired : Bool
    physicalScaleSelectionAndMagnitudeStillRequired : Bool

canonicalDirectSourceVacuumStressBoundary : DirectSourceVacuumStressBoundary
canonicalDirectSourceVacuumStressBoundary =
  direct-source-vacuum-stress-boundary
    true false true false true true true true true false false true

actualSourceVacuumCoefficientFeedsStressDirectly : Bool
actualSourceVacuumCoefficientFeedsStressDirectly =
  Firewall.sourceVacuumReadoutAloneDeterminesPhysicalLambda

publishedVacuumConstantEncodingRequired : Bool
publishedVacuumConstantEncodingRequired =
  Readout.publishedVacuumConstantEncodingStillRequired

metricVolumeSameObjectReceiptRequiredForPhysicalPromotion : Bool
metricVolumeSameObjectReceiptRequiredForPhysicalPromotion = true

cosmologicalRenormalizationReceiptRequiredForPhysicalPromotion : Bool
cosmologicalRenormalizationReceiptRequiredForPhysicalPromotion = true
