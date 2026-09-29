{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTMereologyBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_)\nopen import Data.Product using (_×_; _,_)

import DASHI.Core.ConsumerRelativeMereologyExact as Consumer
import DASHI.Core.MereologyNonCollapseExact as NonCollapse
import DASHI.Physics.Foundations.CMP119AntigravityTraceVsActiveStressFirewallExact as Firewall
import DASHI.Physics.Foundations.CMP119GRAnchoredStressWeldCompilerExact as WeldCompiler
import DASHI.Physics.Foundations.CMP119SingleActiveSectorSourceFactorisationExact as Single
import DASHI.Physics.Foundations.GRQFTActiveGaugeSectorTotalizationExact as Active

------------------------------------------------------------------------
-- GRQFT / ANTIGRAVITY MEREOLOGY BRIDGE
--
-- The symmetric stress carrier has ten independent slots, while the two
-- terminal scalar consumers below require only the four diagonal slots.
-- They consume the SAME four parts with DIFFERENT projections.
------------------------------------------------------------------------

data StressSlot : Set where
  s00 s01 s02 s03 s11 s12 s13 s22 s23 s33 : StressSlot

data StressConsumer : Set where
  fullSymmetricTensor :
    StressConsumer
  lorentzianTraceConsumer :
    StressConsumer
  activeStressConsumer :
    StressConsumer

requiredBy : StressConsumer → StressSlot → Bool
requiredBy fullSymmetricTensor _ = true

requiredBy lorentzianTraceConsumer s00 = true
requiredBy lorentzianTraceConsumer s11 = true
requiredBy lorentzianTraceConsumer s22 = true
requiredBy lorentzianTraceConsumer s33 = true
requiredBy lorentzianTraceConsumer _ = false

requiredBy activeStressConsumer s00 = true
requiredBy activeStressConsumer s11 = true
requiredBy activeStressConsumer s22 = true
requiredBy activeStressConsumer s33 = true
requiredBy activeStressConsumer _ = false

activeConsumerDoesNotRequire01 :
  requiredBy activeStressConsumer s01 ≡ false
activeConsumerDoesNotRequire01 = refl

activeConsumerDoesNotRequire02 :
  requiredBy activeStressConsumer s02 ≡ false
activeConsumerDoesNotRequire02 = refl

activeConsumerDoesNotRequire03 :
  requiredBy activeStressConsumer s03 ≡ false
activeConsumerDoesNotRequire03 = refl

activeConsumerDoesNotRequire12 :
  requiredBy activeStressConsumer s12 ≡ false
activeConsumerDoesNotRequire12 = refl

activeConsumerDoesNotRequire13 :
  requiredBy activeStressConsumer s13 ≡ false
activeConsumerDoesNotRequire13 = refl

activeConsumerDoesNotRequire23 :
  requiredBy activeStressConsumer s23 ≡ false
activeConsumerDoesNotRequire23 = refl

traceAndActiveRequireSameFourSlots :
  ( requiredBy lorentzianTraceConsumer s00
  ≡ requiredBy activeStressConsumer s00 )
  ×
  ( requiredBy lorentzianTraceConsumer s11
  ≡ requiredBy activeStressConsumer s11 )
  ×
  ( requiredBy lorentzianTraceConsumer s22
  ≡ requiredBy activeStressConsumer s22 )
  ×
  ( requiredBy lorentzianTraceConsumer s33
  ≡ requiredBy activeStressConsumer s33 )
traceAndActiveRequireSameFourSlots =
  refl , refl , refl , refl
  where
    open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- SAME PARTS, DIFFERENT WHOLE/PROJECTION
--
-- Reuse the live rational stress theorem rather than restating its algebra.
------------------------------------------------------------------------

traceProjection :
  ℚ → ℚ → ℚ → ℚ → ℚ
traceProjection = Firewall.lorentzianTrace

activeProjection :
  ℚ → ℚ → ℚ → ℚ → ℚ
activeProjection = Firewall.lorentzianActiveStress

activeProjectionIsTracePlusTwiceTimelikePart :
  ∀ rho px py pz →
  activeProjection rho px py pz
  ≡
  traceProjection rho px py pz
    + ((1ℚ + 1ℚ) * rho)
activeProjectionIsTracePlusTwiceTimelikePart =
  Firewall.activeStressIsTracePlusTwiceEnergyDensity

negativeTraceAloneDoesNotCloseActiveConsumer :
  Firewall.negativeTraceAloneClosesNegativeActiveStress ≡ false
negativeTraceAloneDoesNotCloseActiveConsumer =
  Firewall.negativeTraceAloneClosesNegativeActiveStressIsFalse

timelikePartControlStillRequired :
  Firewall.timelikeEnergyDensityControlStillRequired ≡ true
timelikePartControlStillRequired =
  Firewall.timelikeEnergyDensityControlStillRequiredIsTrue

------------------------------------------------------------------------
-- SAME-OBJECT / WELD STATUS
--
-- Component or projection agreement does not manufacture the physical whole.
-- The existing GR-anchored compiler is retained as the theorem owner that
-- consumes the explicit cross-sector stress-weld token.
------------------------------------------------------------------------

sameObjectStressWeldHasSeparateCompiler : Bool
sameObjectStressWeldHasSeparateCompiler = true

sameObjectStressWeldHasSeparateCompilerIsTrue :
  sameObjectStressWeldHasSeparateCompiler ≡ true
sameObjectStressWeldHasSeparateCompilerIsTrue = refl

componentAgreementAloneCreatesStressWeld : Bool
componentAgreementAloneCreatesStressWeld = false

componentAgreementAloneCreatesStressWeldIsFalse :
  componentAgreementAloneCreatesStressWeld ≡ false
componentAgreementAloneCreatesStressWeldIsFalse = refl

crossSectorWeldTokenStillRequired :
  WeldCompiler.crossSectorGRToCMP119StressEqualityRequired ≡ true
crossSectorWeldTokenStillRequired =
  WeldCompiler.crossSectorGRToCMP119StressEqualityRequiredIsTrue

------------------------------------------------------------------------
-- No physical promotion is created by reorganising the part/whole grammar.
------------------------------------------------------------------------

mereologyBridgeCreatesAntigravityEvidence : Bool
mereologyBridgeCreatesAntigravityEvidence = false

mereologyBridgeCreatesAntigravityEvidenceIsFalse :
  mereologyBridgeCreatesAntigravityEvidence ≡ false
mereologyBridgeCreatesAntigravityEvidenceIsFalse = refl

------------------------------------------------------------------------
-- DECLARED SELECTED-PART-AS-WHOLE BOUNDARY
--
-- A single active sector may be the physical total only when the application
-- supplies SingleActiveGaugeSectorTotalization, whose theorem field states
-- declaredTotalIsSelectedSector.  Selection alone does not manufacture the
-- whole.
------------------------------------------------------------------------

activeSectorSelectionPrecedesTotalization :
  Active.activeSectorSelectionPrecedesStressTotalization ≡ true
activeSectorSelectionPrecedesTotalization =
  Active.activeSectorSelectionPrecedesStressTotalizationIsTrue

singleSectorCompilerDoesNotManufactureDeclaredTotal :
  Single.singleSectorCompilerDoesNotManufactureDeclaredTotal ≡ false
singleSectorCompilerDoesNotManufactureDeclaredTotal =
  Single.singleSectorCompilerDoesNotManufactureDeclaredTotalIsFalse

clayUniversalGroupQuantifierIsNotPhysicalFusion :
  Active.clayUniversalGroupParameterMeansAllGroupsPhysicallyActive ≡ false
clayUniversalGroupQuantifierIsNotPhysicalFusion =
  Active.clayUniversalGroupParameterMeansAllGroupsPhysicallyActiveIsFalse
