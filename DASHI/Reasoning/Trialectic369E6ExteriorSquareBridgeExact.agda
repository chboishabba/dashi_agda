module DASHI.Reasoning.Trialectic369E6ExteriorSquareBridgeExact where

------------------------------------------------------------------------
-- 369 / FOUR-TRIT PROVENANCE -> DERIVED EXTERIOR-SQUARE E6 CANDIDATE
--
-- DASHI CONTRIBUTION
--
-- The existing 369 programme owns literal ternary local charts and the T4/T5
-- factorization.  This owner records the correct typed promotion path:
--
--   T4  --choose symplectic structure-->  Lag^±(T4)
--       --primitive exterior square-->   null cone in a five-carrier
--       --same-action recognition-->     E6 mod-3 quadratic candidate.
--
-- It explicitly refuses the shortcut T4^× = null-cone-80.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Foundations.F3SymplecticFourExteriorSquareExact as Exterior
import DASHI.Foundations.F3PrimitiveQuadraticStandardChartExact as Chart
import DASHI.Foundations.E6F3ExteriorSquareRecognitionExact as E6Bridge

record TrialecticFourTritSymplecticAttachment : Set₁ where
  field
    FourTritCarrier : Set
    toV4 : FourTritCarrier → Exterior.V4
    fromV4 : Exterior.V4 → FourTritCarrier
    SymplecticChoice : Set
open TrialecticFourTritSymplecticAttachment public

record TrialecticE6ExteriorSquareWeld
  (attachment : TrialecticFourTritSymplecticAttachment)
  : Set₁ where
  field
    derivedLagrangianRecognition : Exterior.OrientedLagrangianNullRecognition
    e6Model : E6Bridge.E6Mod3QuadraticModel
    sameActionRecognition : E6Bridge.PGSp4WE6Recognition e6Model
    chartReceipt : Chart.PrimitiveStandardIsometryReceipt
open TrialecticE6ExteriorSquareWeld public

record Trialectic369E6ExteriorSquareBoundary : Set where
  constructor trialectic-369-e6-exterior-square-boundary
  field
    existingFourTritProvenanceRetained : Bool
    symplecticStructureIsAdditionalTypedData : Bool
    derivedLag80DistinctFromRawPuncturedT4 : Bool
    exteriorSquareNullRecognitionRequired : Bool
    PGSp4WE6ActionRecognitionRequired : Bool
    cardinality80AloneCreatesWeld : Bool
    E6OntologyRequiredForBaseHyperformalCorrectness : Bool
open Trialectic369E6ExteriorSquareBoundary public

canonicalTrialectic369E6ExteriorSquareBoundary :
  Trialectic369E6ExteriorSquareBoundary
canonicalTrialectic369E6ExteriorSquareBoundary =
  trialectic-369-e6-exterior-square-boundary
    true true true true true
    false false
