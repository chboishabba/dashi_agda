module DASHI.Geometry.Gauge.SUNPrimitives where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

data GeneratorConvention : Set where
  mathAntiHermitian : GeneratorConvention
  physicsHermitian  : GeneratorConvention

data ResidualTag : Set where
  metricResidualTag      : ResidualTag
  determinantResidualTag : ResidualTag
  traceResidualTag       : ResidualTag
  curvatureResidualTag   : ResidualTag
  bianchiResidualTag     : ResidualTag
  centreResidualTag      : ResidualTag

data ResidualStatus : Set where
  zero    : ResidualStatus
  nonzero : ResidualStatus
  unknown : ResidualStatus

record Candidate {ℓ : Level} (A : Set ℓ) : Set (lsuc ℓ) where
  constructor candidate
  field
    label : String

record Proven {ℓ : Level} (A : Set ℓ) : Set (lsuc ℓ) where
  constructor proven
  field
    witness : A

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

clayYangMillsPromotedIsFalse : clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse = refl

data SUNGlobalOpenObligation : Set where
  needsConcreteMatrixCarrier : SUNGlobalOpenObligation
  needsGaugeOrbitQuotient    : SUNGlobalOpenObligation
  needsContinuumLimitControl : SUNGlobalOpenObligation
  needsOSReconstruction      : SUNGlobalOpenObligation
  needsSpectralGapAuthority  : SUNGlobalOpenObligation
