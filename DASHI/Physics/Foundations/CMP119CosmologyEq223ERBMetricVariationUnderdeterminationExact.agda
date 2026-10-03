{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223ERBMetricVariationUnderdeterminationExact where

------------------------------------------------------------------------
-- RAW EQ.(2.23) SECTOR OBJECTS DO NOT FIX THEIR METRIC TRACE.
--
-- The selected source owns literal E/R/B objects, but the current metric
-- realization supplies three derivative maps independently.  Holding the SAME
-- raw source, Wilson derivative, vacuum derivative and reference-measure
-- derivative fixed, one can change only E/R/B derivatives and obtain distinct
-- combined four-diagonal traces.
--
-- Hence a source-native metric-family/first-variation calibration theorem is
-- genuine physical information; Section-2 object identity/localization alone
-- cannot manufacture the cosmological sign envelope.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119CosmologyEq223SourceMetricVariationExact as Eq223
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSectorDecompositionExact as Sector
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw

module _
    {Density Background Fluctuation
     Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum Configuration : Set}
    {source :
      Raw.CMP119SourceNativeRawState
        Density Background Fluctuation
        Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum}
    {scale : Nat}
    (base : Eq223.Eq223SourceMetricVariationRealization source Configuration scale)
  where

  replaceERBMetricVariation :
    (SmallFieldTerm → K.SymmetricTensorComponent4 → Configuration → ℚ) →
    (RTerm → K.SymmetricTensorComponent4 → Configuration → ℚ) →
    (BoundaryTerm → K.SymmetricTensorComponent4 → Configuration → ℚ) →
    Eq223.Eq223SourceMetricVariationRealization source Configuration scale
  replaceERBMetricVariation newE newR newB = record
    { Eq223.Eq223SourceMetricVariationRealization.wilsonMetricVariation =
        Eq223.wilsonMetricVariation base
    ; Eq223.Eq223SourceMetricVariationRealization.regularMetricVariation = newE
    ; Eq223.Eq223SourceMetricVariationRealization.rOperationMetricVariation = newR
    ; Eq223.Eq223SourceMetricVariationRealization.boundaryMetricVariation = newB
    ; Eq223.Eq223SourceMetricVariationRealization.vacuumMetricVariation =
        Eq223.vacuumMetricVariation base
    ; Eq223.Eq223SourceMetricVariationRealization.referenceMeasureLogVariation =
        Eq223.referenceMeasureLogVariation base
    }

  zeroE : SmallFieldTerm → K.SymmetricTensorComponent4 → Configuration → ℚ
  zeroE _ _ _ = 0ℚ

  zeroR : RTerm → K.SymmetricTensorComponent4 → Configuration → ℚ
  zeroR _ _ _ = 0ℚ

  zeroB : BoundaryTerm → K.SymmetricTensorComponent4 → Configuration → ℚ
  zeroB _ _ _ = 0ℚ

  unit00E : SmallFieldTerm → K.SymmetricTensorComponent4 → Configuration → ℚ
  unit00E _ K.component00 _ = 1ℚ
  unit00E _ K.component01 _ = 0ℚ
  unit00E _ K.component02 _ = 0ℚ
  unit00E _ K.component03 _ = 0ℚ
  unit00E _ K.component11 _ = 0ℚ
  unit00E _ K.component12 _ = 0ℚ
  unit00E _ K.component13 _ = 0ℚ
  unit00E _ K.component22 _ = 0ℚ
  unit00E _ K.component23 _ = 0ℚ
  unit00E _ K.component33 _ = 0ℚ

  zeroERBRealization :
    Eq223.Eq223SourceMetricVariationRealization source Configuration scale
  zeroERBRealization = replaceERBMetricVariation zeroE zeroR zeroB

  unitERBRealization :
    Eq223.Eq223SourceMetricVariationRealization source Configuration scale
  unitERBRealization = replaceERBMetricVariation unit00E zeroR zeroB

  combinedERBTrace :
    Eq223.Eq223SourceMetricVariationRealization source Configuration scale →
    Configuration → ℚ
  combinedERBTrace realization configuration =
    let d = Eq223.sourceCompleteFiniteMetricVariation realization
    in
    (Sector.regularDiagonalTrace d configuration
      + Sector.rOperationDiagonalTrace d configuration)
      + Sector.boundaryDiagonalTrace d configuration

  zeroERBTrace :
    ∀ configuration → combinedERBTrace zeroERBRealization configuration ≡ 0ℚ
  zeroERBTrace configuration = refl

  unitERBTrace :
    ∀ configuration → combinedERBTrace unitERBRealization configuration ≡ 1ℚ
  unitERBTrace configuration = refl

  rawEq223SourceAloneFixesCombinedERBMetricTrace : Bool
  rawEq223SourceAloneFixesCombinedERBMetricTrace = false

  sourceBackedERBMetricVariationStillRequired : Bool
  sourceBackedERBMetricVariationStillRequired = true

  section2LocalizationAloneDoesNotDetermineCosmologicalMetricEnvelope : Bool
  section2LocalizationAloneDoesNotDetermineCosmologicalMetricEnvelope = true
