module DASHI.Physics.Closure.NSTriadKNOrderedInteractionTwoChannelMassIdentityRound74Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- DOI: 10.1063/1.858309.
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Classical finite Cauchy--Schwarz inequality; DOI not applicable.
--
-- ROUND74 / CANONICAL Q/W MASS IDENTIFICATION
--
-- For the source-native product z*w, Round74 uses the two real channels
--
--   (Re z, -Im z) dot (Re w, Im w) = Re(z*w).
--
-- The corresponding Cauchy masses are therefore not free weights:
--
--   Q_tau = Re(z)^2 + Im(z)^2,
--   W_tau = Re(w)^2 + Im(w)^2.
--
-- These are exactly the algebraic complex modulus-squared quantities of the
-- literal transport scalar and tested projected response.  This removes the
-- factor-rescaling ambiguity before any analytic frame estimate.
--
-- No positivity/order theorem is needed for these identities; they are exact
-- consequences of the same RealField multiplication/addition used by the
-- physical C3 carrier.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNOrderedInteractionSourceFactorizationRound73Exact as Source
import DASHI.Physics.Closure.NSTriadKNOrderedInteractionRealImaginaryTwoChannelRound74Exact as Channels

complexModulusSquared :
  ∀ {r} {F : C3.RealField r} → C3.Complex F → C3.Carrier F
complexModulusSquared {F = F} (C3.complex real imaginary) =
  C3.add F
    (C3.multiply F real real)
    (C3.multiply F imaginary imaginary)

leftChannelSquaredMass :
  ∀ {r} {F : C3.RealField r} →
  Channels.TwoRealChannels F → C3.Carrier F
leftChannelSquaredMass {F = F} channels =
  C3.add F
    (C3.multiply F (Channels.left0 channels) (Channels.left0 channels))
    (C3.multiply F (Channels.left1 channels) (Channels.left1 channels))

rightChannelSquaredMass :
  ∀ {r} {F : C3.RealField r} →
  Channels.TwoRealChannels F → C3.Carrier F
rightChannelSquaredMass {F = F} channels =
  C3.add F
    (C3.multiply F (Channels.right0 channels) (Channels.right0 channels))
    (C3.multiply F (Channels.right1 channels) (Channels.right1 channels))

leftChannelMassIsTransportModulusSquared :
  ∀ {r} {F : C3.RealField r}
    (z w : C3.Complex F) →
  leftChannelSquaredMass (Channels.sourceProductChannels z w)
  ≡ complexModulusSquared z
leftChannelMassIsTransportModulusSquared {F = F}
    (C3.complex zr zi) (C3.complex wr wi) =
  cong
    (C3.add F (C3.multiply F zr zr))
    (Algebra.realDoubleNegateProduct F zi zi)

rightChannelMassIsResponseModulusSquared :
  ∀ {r} {F : C3.RealField r}
    (z w : C3.Complex F) →
  rightChannelSquaredMass (Channels.sourceProductChannels z w)
  ≡ complexModulusSquared w
rightChannelMassIsResponseModulusSquared
    (C3.complex zr zi) (C3.complex wr wi) = refl

orderedInteractionLeftMassExact :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (incidence : Physical.PhysicalTriadIncidence)
    (testK : C3.Complex3 F) →
  leftChannelSquaredMass
    (Channels.orderedInteractionChannels system incidence testK)
  ≡ complexModulusSquared (Source.transportScalar system incidence)
orderedInteractionLeftMassExact system incidence testK =
  leftChannelMassIsTransportModulusSquared
    (Source.transportScalar system incidence)
    (Source.testedHighResponse system incidence testK)

orderedInteractionRightMassExact :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (incidence : Physical.PhysicalTriadIncidence)
    (testK : C3.Complex3 F) →
  rightChannelSquaredMass
    (Channels.orderedInteractionChannels system incidence testK)
  ≡ complexModulusSquared (Source.testedHighResponse system incidence testK)
orderedInteractionRightMassExact system incidence testK =
  rightChannelMassIsResponseModulusSquared
    (Source.transportScalar system incidence)
    (Source.testedHighResponse system incidence testK)

round74TwoChannelChargeIsLiteralTransportModulusSquared : Bool
round74TwoChannelChargeIsLiteralTransportModulusSquared = true

round74TwoChannelComplexityIsLiteralResponseModulusSquared : Bool
round74TwoChannelComplexityIsLiteralResponseModulusSquared = true

round74FactorRescalingAmbiguityRemovedAtLiteralSource : Bool
round74FactorRescalingAmbiguityRemovedAtLiteralSource = true

round74PhysicalFrameBoundOnResponseModulusSquaredConstructed : Bool
round74PhysicalFrameBoundOnResponseModulusSquaredConstructed = false

round74FactorRescalingAmbiguityRemovedAtLiteralSourceIsTrue :
  round74FactorRescalingAmbiguityRemovedAtLiteralSource ≡ true
round74FactorRescalingAmbiguityRemovedAtLiteralSourceIsTrue = refl
