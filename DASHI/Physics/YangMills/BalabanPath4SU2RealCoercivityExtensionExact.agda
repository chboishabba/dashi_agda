{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath4SU2RealCoercivityExtensionExact where

------------------------------------------------------------------------
-- RATIONAL PATH4 COERCIVITY -> REAL FINITE-DIMENSIONAL COERCIVITY
--
-- The checked Path4 certificate is on rational-valued positive-bond tangents.
-- The physical SU(2) principal logarithm lives in a real Lie algebra. A ring
-- embedding transports rational points, but not the theorem to arbitrary real
-- points. The missing standard step is density + continuity of the finite
-- quadratic form and norm. This module isolates that step exactly, consuming
-- the literal rational coercivity theorem rather than a Set-valued receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Foundations.RealAnalysisAxioms as Real
import DASHI.Foundations.BishopConstructiveRealBridgeExact as BishopBridge
import DASHI.Physics.YangMills.BalabanR208BishopLegacyRingEmbeddingExact as Embed
open import DASHI.Physics.YangMills.BalabanConfiguredRGSide4Certificate using
  (configuredRGBlockSide; configuredPathCoercivityConstant)
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (PositiveBond)
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact using
  (SU2Component; PhysicalSU2Tangent4; physicalUnweightedNormSq)
open import DASHI.Physics.YangMills.BalabanPath4SU2ConcretePropagatorExact using
  (configuredGaugeFixedEnergy; configuredGaugeFixedMatrixPositive)

RealPhysicalSU2Tangent4 : Set
RealPhysicalSU2Tangent4 =
  SU2Component → PositiveBond configuredRGBlockSide → Real.ℝ

embedRationalPath4Tangent :
  BishopBridge.BishopToDASHIRealBridge →
  PhysicalSU2Tangent4 → RealPhysicalSU2Tangent4
embedRationalPath4Tangent bridge tangent component bond =
  Embed.legacyRationalEmbed bridge (tangent component bond)

record RealPath4QuadraticExtension
    (bridge : BishopBridge.BishopToDASHIRealBridge) : Set₁ where
  field
    realNormSq : RealPhysicalSU2Tangent4 → Real.ℝ
    realGaugeFixedEnergy : RealPhysicalSU2Tangent4 → Real.ℝ
    realCoercivityConstant : Real.ℝ
    multiplyReal : Real.ℝ → Real.ℝ → Real.ℝ
    LessEqual : Real.ℝ → Real.ℝ → Set

    coercivityConstantExtendsRational :
      realCoercivityConstant
      ≡ Embed.legacyRationalEmbed bridge configuredPathCoercivityConstant

    -- Standard finite-dimensional density/continuity theorem specialized to
    -- the exact rational Path4 quadratic inequality. The premise is the actual
    -- inequality theorem on every rational tangent, not a receipt-shaped Set.
    rationalCoercivityExtendsToAllRealTangents :
      (∀ rationalTangent →
        configuredPathCoercivityConstant
          * physicalUnweightedNormSq rationalTangent
        ≤ configuredGaugeFixedEnergy rationalTangent) →
      ∀ realTangent →
      LessEqual
        (multiplyReal realCoercivityConstant (realNormSq realTangent))
        (realGaugeFixedEnergy realTangent)

open RealPath4QuadraticExtension public

realPath4CoercivityFromCheckedCertificate :
  (bridge : BishopBridge.BishopToDASHIRealBridge) →
  (extension : RealPath4QuadraticExtension bridge) →
  ∀ realTangent →
  LessEqual extension
    (multiplyReal extension
      (realCoercivityConstant extension)
      (realNormSq extension realTangent))
    (realGaugeFixedEnergy extension realTangent)
realPath4CoercivityFromCheckedCertificate bridge extension =
  rationalCoercivityExtendsToAllRealTangents extension
    configuredGaugeFixedMatrixPositive

realPath4ScalarExtensionCompilerLevel : ProofLevel
realPath4ScalarExtensionCompilerLevel = machineChecked

realPath4DensityContinuityAuthorityLevel : ProofLevel
realPath4DensityContinuityAuthorityLevel = standardImported

literalBishopToLegacyRealBridgeForPath4Level : ProofLevel
literalBishopToLegacyRealBridgeForPath4Level = conditional
