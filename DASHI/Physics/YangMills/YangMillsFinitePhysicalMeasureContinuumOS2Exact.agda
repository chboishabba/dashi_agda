{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureContinuumOS2Exact where

------------------------------------------------------------------------
-- FINITE PHYSICAL YM FAMILY -> POSITIVE NORMALIZED CONTINUUM MEASURE + OS2
------------------------------------------------------------------------

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as PhysicalLimit
import DASHI.Physics.YangMills.YangMillsCylinderLimitOSReflectionPositiveExact as OS2
import DASHI.Physics.YangMills.BalabanClayT5OSGramTopologyExact as GramOS
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram

record FinitePhysicalMeasureContinuumOS2Inputs
    (Configuration : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit)
    (quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit))
    (division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient) : Set₁ where
  field
    family :
      PhysicalLimit.FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division

    observableAlgebra :
      OS2.CylinderOSAlgebra (Configuration → ℝ)

    finiteReflectionPositive :
      ∀ cutoff
        (testFamily :
          Gram.PhysicalOSFiniteTestFamily (Configuration → ℝ) ℝ) →
      0ℝ ≤ℝ
      Gram.physicalReflectedGramQuadraticForm
        (OS2.operations observableAlgebra)
        (λ observable →
          PhysicalLimit.finiteExpectation family cutoff observable)
        testFamily

open FinitePhysicalMeasureContinuumOS2Inputs public

asCylinderOSInputs :
  ∀ {Configuration sequenceLimit limitLaws quotient division} →
  (inputs :
    FinitePhysicalMeasureContinuumOS2Inputs
      Configuration limitLaws quotient division) →
  OS2.CylinderLimitOSInputs
    limitLaws
    (PhysicalLimit.asCylinderLimitData (family inputs))
    (observableAlgebra inputs)
asCylinderOSInputs inputs = record
  { OS2.CylinderLimitOSInputs.finiteReflectionPositive =
      finiteReflectionPositive inputs
  }

continuumReflectionPositive :
  ∀ {Configuration sequenceLimit limitLaws quotient division}
    (inputs :
      FinitePhysicalMeasureContinuumOS2Inputs
        Configuration limitLaws quotient division) →
  GramOS.GramReflectionPositive
    (OS2.asOSGramLimitData (asCylinderOSInputs inputs))
    (PhysicalLimit.limitExpectation (family inputs))
continuumReflectionPositive inputs =
  OS2.continuumReflectionPositive
    (asCylinderOSInputs inputs)

finitePhysicalToContinuumOS2CompilerLevel : ProofLevel
finitePhysicalToContinuumOS2CompilerLevel = machineChecked

-- The remaining inputs are literal finite physics:
-- Haar integration/normalization/nonzero partition and Wilson RP.
literalFinitePhysicalMeasureInputsLevel : ProofLevel
literalFinitePhysicalMeasureInputsLevel = conditional
