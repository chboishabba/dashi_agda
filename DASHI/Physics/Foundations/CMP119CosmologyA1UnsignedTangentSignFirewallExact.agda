{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyA1UnsignedTangentSignFirewallExact where

------------------------------------------------------------------------
-- A1 SIGN FIREWALL.
--
-- The present-cut finite tangent is definitionally the ten-element carrier of
-- symmetric component labels.  It does not itself carry a scalar coefficient.
-- But the actual hypercubic rank-two action is signed: e.g. flip0 sends the
-- 01 basis tensor to -01 while leaving 00 positive.
--
-- Therefore a proof that merely permutes the unsigned tangent labels cannot by
-- itself establish the physical B4 covariance theorem.  The source-facing A1
-- theorem must retain the signed R144 readout covariance (or an equivalent
-- differentiated source law that explicitly transports this basis sign).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119CosmologyE1SignedSymmetricTangentExact as Signed
import DASHI.Physics.Foundations.CMP119CosmologyE1HypercubicSignedAxisActionExact as Axis
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Hyper

flip0ActsWithNegativeSignOn01 :
  Signed.actSignedComponent
    (Axis.hypercubicSignedAxisAction Hyper.flip0)
    K.component01
  ≡ Signed.signed-component Signed.minus K.component01
flip0ActsWithNegativeSignOn01 = Axis.flip0Flips01

flip0ActsWithPositiveSignOn00 :
  Signed.actSignedComponent
    (Axis.hypercubicSignedAxisAction Hyper.flip0)
    K.component00
  ≡ Signed.signed-component Signed.plus K.component00
flip0ActsWithPositiveSignOn00 = Axis.flip0Keeps00

presentTangentCarrierIsUnsignedTenSlot : Bool
presentTangentCarrierIsUnsignedTenSlot = true

hypercubicReflectionsCarryIndependentBasisSign : Bool
hypercubicReflectionsCarryIndependentBasisSign = true

unsignedComponentPermutationAlonePaysA1 : Bool
unsignedComponentPermutationAlonePaysA1 = false

terminalA1SourceLawMustBeSignedReadoutCovariance : Bool
terminalA1SourceLawMustBeSignedReadoutCovariance = true
