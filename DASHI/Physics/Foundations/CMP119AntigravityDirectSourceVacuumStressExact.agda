{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityDirectSourceVacuumStressExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Closure.SymbolicEinsteinHilbertModel as EH
import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Stress
import DASHI.Physics.Foundations.GRQFTVacuumStressLambdaCompilerExact as VacuumStress
import DASHI.Physics.Foundations.CMP119AntigravityLocalizedVacuumReadoutExact as Readout
import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as Source
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4

------------------------------------------------------------------------
-- DIRECT SOURCE VACUUM -> COSMOLOGICAL STRESS
--
-- The older source-native compiler was packaged around one fixed two-amplitude
-- receipt.  For design search that is unnecessary.  On the concrete
-- LocalizedAction source we can read the ACTUAL vacuum coefficient at any scale
-- and feed it directly into the already-proved vacuum stress ray
--
--      T_mu_nu(lambda) = - lambda g_mu_nu.
--
-- This route does not require the separately pinned normalized CMP119 stress
-- tensor and does not require 21/64 or 19/48.  It uses the source's literal
-- vacuumEnergy object, the existing source projector, and the existing GRQFT
-- vacuum-stress compiler.
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

  sourceVacuumStressIsMinusLambdaMetric :
    ∀ scale (a b : Flat.Axis4) →
    sourceVacuumStressAtScale scale a b
    ≡ Readout.localizedVacuumValue source scale
        Data.Rational.Base.* VacuumStress.negativeMetric a b
  sourceVacuumStressIsMinusLambdaMetric scale a b =
    VacuumStress.vacuumStressIsMinusLambdaMetric
      (Readout.localizedVacuumValue source scale) a b

record DirectSourceVacuumStressBoundary : Set where
  constructor direct-source-vacuum-stress-boundary
  field
    actualSourceVacuumCoefficientFeedsStressDirectly : Bool
    symbolicVacuumVariationShapeAlreadyOwned : Bool
    fixedAmplitudeReceiptRequired : Bool
    pinnedNormalizedStressTensorRequired : Bool
    independentCosmologicalStressShapeRequired : Bool
    physicalScaleSelectionAndMagnitudeStillRequired : Bool

canonicalDirectSourceVacuumStressBoundary : DirectSourceVacuumStressBoundary
canonicalDirectSourceVacuumStressBoundary =
  direct-source-vacuum-stress-boundary
    true true false false false true
