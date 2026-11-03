{-# OPTIONS --safe #-}
module DASHI.Physics.ExoticGravity.AntigravityPostNormalizationDirectStressMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119AntigravityLocalCWightmanDirectStressGeometryExact as Static
import DASHI.Physics.Foundations.CMP119AntigravityLocalCWightmanDirectStressDifferentialExact as Differential
import DASHI.Physics.ExoticGravity.AntigravitySICalibrationDonorMaxCutExact as SI

------------------------------------------------------------------------
-- POST-NORMALIZATION DIRECT-STRESS MAX-CUT
--
-- Preferred route after the typed Local-C/Wightman terminal is available:
-- consume the reconstructed Lorentzian vacuum stress itself.
--
-- Static:
--   rho_terminal > 0 -> normalized safe static geometry.
--
-- Differential:
--   two terminal stresses + ONE common cosmological renormalization convention
--     -> Delta Lambda_norm = rho_on - rho_off
--     -> scalar Kottler metric difference.
--
-- Therefore the affine scalar-normalization map
--
--   rho = a V + c
--
-- is NOT mandatory on this preferred stress-first route.  It remains a useful
-- optional source-coordinate attribution route when V itself is the consumer.
--
-- Genuine common P2 physical payments left after current repo reuse:
--   1. the cosmological renormalization convention for the absolute/shared
--      vacuum-stress zero;
--   2. the same-apparatus physical stress*length^2 scale.
--
-- Accepted measured G and the target-interval algebra are already paid.
------------------------------------------------------------------------

preferredRouteConsumesTypedLocalCWightmanStressDirectly : Bool
preferredRouteConsumesTypedLocalCWightmanStressDirectly = true

affineSourceNormalizationCalibrationRequiredForPreferredRoute : Bool
affineSourceNormalizationCalibrationRequiredForPreferredRoute = false

directStaticNormalizedGeometryCompilerOwned : Bool
directStaticNormalizedGeometryCompilerOwned = true

directScalarDifferentialCompilerOwned : Bool
directScalarDifferentialCompilerOwned = true

acceptedMeasuredGStillRequired : Bool
acceptedMeasuredGStillRequired =
  SI.acceptedMeasuredGAuthorityStillRequired

commonCosmologicalRenormalizationStillRequired : Bool
commonCosmologicalRenormalizationStillRequired = true

stressLengthSquaredScaleStillRequired : Bool
stressLengthSquaredScaleStillRequired =
  SI.sourceStressLengthSquaredScaleStillRequired

remainingPreferredP2PhysicalLeafCount : Nat
remainingPreferredP2PhysicalLeafCount = 2

sourceNormalizationAffineRouteStillAvailable : Bool
sourceNormalizationAffineRouteStillAvailable = true

scalarDifferentialAlreadyPromotesToTT : Bool
scalarDifferentialAlreadyPromotesToTT = false
