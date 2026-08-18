module DASHI.Physics.Closure.NSTriadKNOrderedInteractionRealImaginaryTwoChannelRound74Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- ROUND74 / PHASE-FREE SOURCE FACTORIZATION
--
-- Round73 exposed the exact same-incidence complex product
--
--   z_tau w_tau
--
-- with
--
--   z_tau = -i (u_p dot q),
--   w_tau = <test_k, P_k u_q>.
--
-- A first sufficient compiler asked for a cancelling phase
-- z=x theta, w=y conjugate(theta).  That is unnecessarily strong.  The real
-- signed coefficient has the canonical algebraic decomposition
--
--   Re(z w) = Re(z) Re(w) - Im(z) Im(w).
--
-- Thus every literal ordered interaction has TWO source-native real channels,
-- with no phase choice and no rescaling authority:
--
--   channel 0 :  Re(z) * Re(w)
--   channel 1 : (-Im(z)) * Im(w).
--
-- This is the natural finite-Cauchy carrier.  Waleffe's helical triad analysis
-- is useful physical context for polarization/geometry, but no helical phase
-- locking is assumed or required by this algebraic reduction.
--
-- Remaining physical work: transport these exact real-carrier channels into
-- the ordered scalar/energy carrier used by Q,W and prove the corresponding
-- frame/charge bounds.  `PhysicalOrderedInteractionPhaseAlignment` is thereby
-- demoted from a mandatory frontier theorem.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as Signed
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNOrderedInteractionSourceFactorizationRound73Exact as Source

realProductCoordinate :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex F → C3.Complex F → C3.Carrier F
realProductCoordinate {F = F}
    (C3.complex zr zi) (C3.complex wr wi) =
  C3.add F
    (C3.multiply F zr wr)
    (C3.negate F (C3.multiply F zi wi))

realProductCoordinateExact :
  ∀ {r} {F : C3.RealField r}
    (z w : C3.Complex F) →
  C3.complexRealPart (C3.complexMultiply z w)
  ≡ C3.realEmbed F (realProductCoordinate z w)
realProductCoordinateExact (C3.complex zr zi) (C3.complex wr wi) = refl

record TwoRealChannels {r : Level} (F : C3.RealField r) : Set r where
  constructor two-real-channels
  field
    left0 right0 left1 right1 : C3.Carrier F

open TwoRealChannels public

sourceProductChannels :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex F → C3.Complex F → TwoRealChannels F
sourceProductChannels {F = F}
    (C3.complex zr zi) (C3.complex wr wi) =
  two-real-channels zr wr (C3.negate F zi) wi

channelTotal :
  ∀ {r} {F : C3.RealField r} →
  TwoRealChannels F → C3.Carrier F
channelTotal {F = F} channels =
  C3.add F
    (C3.multiply F (left0 channels) (right0 channels))
    (C3.multiply F (left1 channels) (right1 channels))

sourceProductChannelsExact :
  ∀ {r} {F : C3.RealField r}
    (z w : C3.Complex F) →
  realProductCoordinate z w
  ≡ channelTotal (sourceProductChannels z w)
sourceProductChannelsExact {F = F}
    (C3.complex zr zi) (C3.complex wr wi) =
  cong
    (C3.add F (C3.multiply F zr wr))
    (C3.negateMultiplyLeft F zi wi)

orderedInteractionChannels :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence →
  C3.Complex3 F → TwoRealChannels F
orderedInteractionChannels system incidence testK =
  sourceProductChannels
    (Source.transportScalar system incidence)
    (Source.testedHighResponse system incidence testK)

signedCoefficientIsTwoChannelRealProduct :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (incidence : Physical.PhysicalTriadIncidence)
    (testK : C3.Complex3 F) →
  Signed.testedSignedCoefficient
    (Audit.galerkinLaws system)
    (Physical.k incidence)
    (Physical.p incidence)
    (Physical.q incidence)
    (Audit.velocityAt system (Physical.p incidence))
    (Audit.velocityAt system (Physical.q incidence))
    testK
  ≡
  C3.realEmbed F
    (channelTotal (orderedInteractionChannels system incidence testK))
signedCoefficientIsTwoChannelRealProduct system incidence testK =
  let
    z = Source.transportScalar system incidence
    w = Source.testedHighResponse system incidence testK
  in
  trans
    (Source.signedCoefficientIsRealPartOfSourceProduct system incidence testK)
    (trans
      (realProductCoordinateExact z w)
      (cong (C3.realEmbed _)
        (sourceProductChannelsExact z w)))

round74LiteralSignedCoefficientHasCanonicalTwoRealChannels : Bool
round74LiteralSignedCoefficientHasCanonicalTwoRealChannels = true

round74PhysicalPhaseAlignmentRequiredForFactorization : Bool
round74PhysicalPhaseAlignmentRequiredForFactorization = false

round74TwoChannelScalarEnergyTransportConstructed : Bool
round74TwoChannelScalarEnergyTransportConstructed = false

round74LiteralSignedCoefficientHasCanonicalTwoRealChannelsIsTrue :
  round74LiteralSignedCoefficientHasCanonicalTwoRealChannels ≡ true
round74LiteralSignedCoefficientHasCanonicalTwoRealChannelsIsTrue = refl

round74PhysicalPhaseAlignmentRequiredForFactorizationIsFalse :
  round74PhysicalPhaseAlignmentRequiredForFactorization ≡ false
round74PhysicalPhaseAlignmentRequiredForFactorizationIsFalse = refl
