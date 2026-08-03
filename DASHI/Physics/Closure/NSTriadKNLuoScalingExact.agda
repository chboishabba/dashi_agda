module DASHI.Physics.Closure.NSTriadKNLuoScalingExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Author: Edgar Buckingham.
-- Title: "On Physically Similar Systems; Illustrations of the Use of
-- Dimensional Equations".
-- Physical Review 4 (1914), 345--376.
-- DOI: 10.1103/PhysRev.4.345.
--
-- PURPOSE
-- Connect the official periodic Luo source carrier to a general (L,U)
-- normalization.  The scale identity
--
--   (U/L) (L/U) = 1
--
-- proves that the localized integral of ||grad u_{<=p}||_infinity is unchanged.
-- The unit-viscosity source is represented as the special viscous/Re=1 scale
-- selection U = nu/L, rather than being baked into the foundational algebra.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSTriadKNLuoOfficialLerayHopfAuthorityExact as Official
import DASHI.Physics.Units.PhysicalNormalizationExact as Normalize
open import DASHI.Physics.YangMills.CompactLieProofLevel

record OfficialLuoPhysicalScaling
    {d s t : Level}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    (carrier : Official.OfficialPeriodicLuoSourceCarrier
      InitialDatum Solution Time) : Set (lsuc (d ⊔ s ⊔ t)) where
  field
    scaleAlgebra : Normalize.ScaleAlgebra ℚ

    lengthScale : Normalize.PositiveScale scaleAlgebra
    velocityScale : Normalize.PositiveScale scaleAlgebra
    viscosityScale : Normalize.PositiveScale scaleAlgebra

    viscousVelocitySelection :
      Normalize.ViscousVelocitySelection
        scaleAlgebra lengthScale velocityScale viscosityScale

    normalizedLocalizedGradientIntegral :
      Solution → Time → Nat → ℚ

    normalizedIntegralMatchesOfficial :
      (solution : Solution) →
      (terminal : Time) →
      (shell : Nat) →
      normalizedLocalizedGradientIntegral solution terminal shell
      ≡ Official.localizedGradientIntegral carrier solution terminal shell

    physicalLocalizedGradientIntegral :
      Solution → Time → Nat → ℚ

    physicalIntegralDefinition :
      (solution : Solution) →
      (terminal : Time) →
      (shell : Nat) →
      physicalLocalizedGradientIntegral solution terminal shell
      ≡ Normalize.scaledLocalizedIntegral
          scaleAlgebra lengthScale velocityScale
          (normalizedLocalizedGradientIntegral solution terminal shell)

open OfficialLuoPhysicalScaling public

luoLocalizedGradientIntegralScaleInvariant :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {carrier : Official.OfficialPeriodicLuoSourceCarrier
      InitialDatum Solution Time} →
  (scaling : OfficialLuoPhysicalScaling carrier) →
  (solution : Solution) →
  (terminal : Time) →
  (shell : Nat) →
  physicalLocalizedGradientIntegral scaling solution terminal shell
  ≡ Official.localizedGradientIntegral carrier solution terminal shell
luoLocalizedGradientIntegralScaleInvariant scaling solution terminal shell =
  trans
    (physicalIntegralDefinition scaling solution terminal shell)
    (trans
      (Normalize.localizedIntegralScaleInvariant
        (scaleAlgebra scaling)
        (lengthScale scaling)
        (velocityScale scaling)
        (normalizedLocalizedGradientIntegral scaling solution terminal shell))
      (normalizedIntegralMatchesOfficial scaling solution terminal shell))

luoReynoldsOneSelection :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {carrier : Official.OfficialPeriodicLuoSourceCarrier
      InitialDatum Solution Time} →
  (scaling : OfficialLuoPhysicalScaling carrier) →
  Normalize.ReynoldsOneSelection
    (scaleAlgebra scaling)
    (lengthScale scaling)
    (velocityScale scaling)
    (viscosityScale scaling)
luoReynoldsOneSelection scaling =
  Normalize.luoUnitViscosityIsSpecialSelection
    (viscousVelocitySelection scaling)

luoSourceNormalizationStillUsesOfficialCarrier :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  (carrier : Official.OfficialPeriodicLuoSourceCarrier
    InitialDatum Solution Time) →
  Official.SourceNormalizationMatchesLuo carrier
luoSourceNormalizationStillUsesOfficialCarrier =
  Official.selectedSourceNormalization

luoScalingAlgebraLevel : ProofLevel
luoScalingAlgebraLevel = machineChecked

luoLocalizedIntegralInvarianceLevel : ProofLevel
luoLocalizedIntegralInvarianceLevel = machineChecked

luoContinuationAuthorityLevel : ProofLevel
luoContinuationAuthorityLevel = standardImported
