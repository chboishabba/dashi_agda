{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsContinuumSchwingerFromMeasureExact where

------------------------------------------------------------------------
-- SAME-OBJECT CONTINUUM SCHWINGER FAMILY FROM THE CONTINUUM MEASURE
--
-- The Schwinger family is not selected independently.  A declared cylinder
-- encoding of the two-point insertion is evaluated by the SAME continuum
-- expectation functional.
------------------------------------------------------------------------

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

record CylinderSchwingerEncoding
    (Observable Position : Set) : Set₁ where
  field
    twoPointCylinder :
      Observable → Position → Position → Observable

open CylinderSchwingerEncoding public

schwingerFromMeasure :
  ∀ {Observable Position} →
  CylinderSchwingerEncoding Observable Position →
  Physical.PhysicalContinuumYMMeasure Observable ℝ →
  Physical.PhysicalSchwingerFamily Observable Position ℝ
schwingerFromMeasure encoding measure =
  Physical.physicalSchwingerFamily
    (λ observable left right →
      Physical.expectation measure
        (twoPointCylinder encoding observable left right))

schwingerValueIsMeasureExpectation :
  ∀ {Observable Position}
    (encoding : CylinderSchwingerEncoding Observable Position)
    (measure : Physical.PhysicalContinuumYMMeasure Observable ℝ)
    observable left right →
  Physical.schwinger
    (schwingerFromMeasure encoding measure)
    observable left right
  ≡
  Physical.expectation measure
    (twoPointCylinder encoding observable left right)
schwingerValueIsMeasureExpectation encoding measure observable left right =
  Agda.Builtin.Equality.refl

continuumSchwingerFromMeasureCompilerLevel : ProofLevel
continuumSchwingerFromMeasureCompilerLevel = machineChecked

-- Literal physics remaining: the cylinder encoding must be proved to be the
-- intended gauge-invariant continuum insertion on the physical configuration
-- carrier.
literalCylinderSchwingerEncodingMeaningLevel : ProofLevel
literalCylinderSchwingerEncodingMeaningLevel = conditional
