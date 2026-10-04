{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223VacuumMetricSignUnderdeterminationExact where

------------------------------------------------------------------------
-- EQ.(2.23) VACUUM OBJECT DOES NOT BY ITSELF FIX THE METRIC WEYL SIGN.
--
-- `CMP119SourceNativeRawState` selects the literal vacuum term in the complete
-- action.  The current metric realization supplies separately
--
--   vacuumMetricVariation : Vacuum -> SymmetricComponent4 -> Q.
--
-- Consequently the raw Eq.(2.23) assembly alone cannot determine c_V.  Holding
-- the SAME source and every non-vacuum metric derivative fixed, one can replace
-- only the vacuum metric derivative and obtain zero, positive or negative Weyl
-- trace coefficients.
--
-- This is a representation/metric-variation firewall, not a claim that the
-- physical CMP119 vacuum derivative is arbitrary.  It proves exactly why a
-- source-backed vacuum metric-variation theorem is still required.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; -_)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119CosmologyEq223SourceMetricVariationExact as Eq223
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

  replaceVacuumMetricVariation :
    (Vacuum → K.SymmetricTensorComponent4 → ℚ) →
    Eq223.Eq223SourceMetricVariationRealization source Configuration scale
  replaceVacuumMetricVariation newVacuum = record
    { Eq223.Eq223SourceMetricVariationRealization.wilsonMetricVariation =
        Eq223.wilsonMetricVariation base
    ; Eq223.Eq223SourceMetricVariationRealization.regularMetricVariation =
        Eq223.regularMetricVariation base
    ; Eq223.Eq223SourceMetricVariationRealization.rOperationMetricVariation =
        Eq223.rOperationMetricVariation base
    ; Eq223.Eq223SourceMetricVariationRealization.boundaryMetricVariation =
        Eq223.boundaryMetricVariation base
    ; Eq223.Eq223SourceMetricVariationRealization.vacuumMetricVariation =
        newVacuum
    ; Eq223.Eq223SourceMetricVariationRealization.referenceMeasureLogVariation =
        Eq223.referenceMeasureLogVariation base
    }

  zeroVacuumMetricVariation :
    Vacuum → K.SymmetricTensorComponent4 → ℚ
  zeroVacuumMetricVariation _ _ = 0ℚ

  positive00VacuumMetricVariation :
    Vacuum → K.SymmetricTensorComponent4 → ℚ
  positive00VacuumMetricVariation _ K.component00 = 1ℚ
  positive00VacuumMetricVariation _ K.component01 = 0ℚ
  positive00VacuumMetricVariation _ K.component02 = 0ℚ
  positive00VacuumMetricVariation _ K.component03 = 0ℚ
  positive00VacuumMetricVariation _ K.component11 = 0ℚ
  positive00VacuumMetricVariation _ K.component12 = 0ℚ
  positive00VacuumMetricVariation _ K.component13 = 0ℚ
  positive00VacuumMetricVariation _ K.component22 = 0ℚ
  positive00VacuumMetricVariation _ K.component23 = 0ℚ
  positive00VacuumMetricVariation _ K.component33 = 0ℚ

  negative00VacuumMetricVariation :
    Vacuum → K.SymmetricTensorComponent4 → ℚ
  negative00VacuumMetricVariation _ K.component00 = - 1ℚ
  negative00VacuumMetricVariation _ K.component01 = 0ℚ
  negative00VacuumMetricVariation _ K.component02 = 0ℚ
  negative00VacuumMetricVariation _ K.component03 = 0ℚ
  negative00VacuumMetricVariation _ K.component11 = 0ℚ
  negative00VacuumMetricVariation _ K.component12 = 0ℚ
  negative00VacuumMetricVariation _ K.component13 = 0ℚ
  negative00VacuumMetricVariation _ K.component22 = 0ℚ
  negative00VacuumMetricVariation _ K.component23 = 0ℚ
  negative00VacuumMetricVariation _ K.component33 = 0ℚ

  zeroRealization :
    Eq223.Eq223SourceMetricVariationRealization source Configuration scale
  zeroRealization = replaceVacuumMetricVariation zeroVacuumMetricVariation

  positiveRealization :
    Eq223.Eq223SourceMetricVariationRealization source Configuration scale
  positiveRealization =
    replaceVacuumMetricVariation positive00VacuumMetricVariation

  negativeRealization :
    Eq223.Eq223SourceMetricVariationRealization source Configuration scale
  negativeRealization =
    replaceVacuumMetricVariation negative00VacuumMetricVariation

  zeroVacuumWeylCoefficient :
    Eq223.eq223VacuumTraceCoefficient zeroRealization ≡ 0ℚ
  zeroVacuumWeylCoefficient = refl

  positiveVacuumWeylCoefficient :
    Eq223.eq223VacuumTraceCoefficient positiveRealization ≡ 1ℚ
  positiveVacuumWeylCoefficient = refl

  negativeVacuumWeylCoefficient :
    Eq223.eq223VacuumTraceCoefficient negativeRealization ≡ - 1ℚ
  negativeVacuumWeylCoefficient = refl

  rawEq223SourceAloneFixesVacuumMetricSign : Bool
  rawEq223SourceAloneFixesVacuumMetricSign = false

  sourceBackedVacuumMetricVariationStillRequired : Bool
  sourceBackedVacuumMetricVariationStillRequired = true

  changingVacuumMetricDerivativeLeavesAllOtherMetricDerivativeFieldsUntouched : Bool
  changingVacuumMetricDerivativeLeavesAllOtherMetricDerivativeFieldsUntouched = true
