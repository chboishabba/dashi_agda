module DASHI.Physics.Closure.NSTriadKNStaticRationalTwoChannelOverlayRound75Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- DOI: 10.1063/1.858309.
--
-- ROUND75 / LITERAL RATIONAL GALERKIN ROW -> ROUND74 TWO-CHANNEL OVERLAY
--
-- Round72's StaticPhysicalShellPairing retained a free rational `triadValue`.
-- Round74 proved the literal complex Galerkin coefficient has the canonical
-- two-channel identity
--
--   Re(z w) = Re(z)Re(w) - Im(z)Im(w),
--
-- but the structured rational overlay had not yet been connected to the
-- literal finite Galerkin system.
--
-- Here the static pairing's triad value IS DEFINED from the exact rational C3
-- Galerkin coefficient, tested against the output velocity itself.  The global
-- pairing is then the existing five-source total of those same values.
--
-- On the exact same classified physical output-fibre list, we recursively
-- construct Round74's `TriadicTwoChannelOverlay`.  Each overlay equality comes
-- directly from the literal source product theorem; no phase, rescaling, or
-- separately supplied scalar factorization remains.
--
-- HH owner selection remains the same explicit Round72 physical classification
-- obligation.  Time dependence remains separate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as RationalL2
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as Signed
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as Support
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSumRound25Exact as Five
import DASHI.Physics.Closure.NSTriadKNGlobalBilinearShellPairingRound29Exact as Shell
import DASHI.Physics.Closure.NSTriadKNStaticPairingEmitsStructuredTriadicAtomsRound72Exact as Fine
import DASHI.Physics.Closure.NSTriadKNOrderedInteractionRealImaginaryTwoChannelRound74Exact as Channels
import DASHI.Physics.Closure.NSTriadKNTwoChannelStructuredCauchyOverlayRound74Exact as Overlay

F : C3.RealField _
F = RationalL2.rationalRealField

outputVelocityTest :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
outputVelocityTest system incidence =
  Audit.velocityAt system (Physical.k incidence)

literalRationalTriadValue :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → ℚ
literalRationalTriadValue system incidence =
  C3.real
    (Signed.testedSignedCoefficient
      (Audit.galerkinLaws system)
      (Physical.k incidence)
      (Physical.p incidence)
      (Physical.q incidence)
      (Audit.velocityAt system (Physical.p incidence))
      (Audit.velocityAt system (Physical.q incidence))
      (outputVelocityTest system incidence))

literalRationalTriadValueIsChannelTotal :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (incidence : Physical.PhysicalTriadIncidence) →
  literalRationalTriadValue system incidence
  ≡ Channels.channelTotal
      (Channels.orderedInteractionChannels
        system incidence (outputVelocityTest system incidence))
literalRationalTriadValueIsChannelTotal system incidence =
  cong C3.real
    (Channels.signedCoefficientIsTwoChannelRealProduct
      system incidence (outputVelocityTest system incidence))

staticRationalPhysicalPairing :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (output : Z3.FourierMode) →
  (commutatorValue : Z3.FourierMode → ℚ) →
  Shell.StaticPhysicalShellPairing
staticRationalPhysicalPairing system output commutatorValue =
  Shell.static-physical-shell-pairing
    (Audit.cutoff system)
    output
    (literalRationalTriadValue system)
    commutatorValue
    (Five.fiveSourceTotal
      (Audit.cutoff system)
      output
      (literalRationalTriadValue system)
      commutatorValue)
    refl

channelsForClassified :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Support.ClassifiedPhysicalTriad → Channels.TwoRealChannels F
channelsForClassified system classified =
  let incidence = Support.incidence classified in
  Channels.orderedInteractionChannels
    system incidence (outputVelocityTest system incidence)

twoChannelOverlayFromClassified :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (pairing : Shell.StaticPhysicalShellPairing)
    (hh : Fine.HHOwnerSelection)
    (classified : List Support.ClassifiedPhysicalTriad) →
  (∀ selected → Shell.triadValue pairing (Support.incidence selected)
      ≡ literalRationalTriadValue system (Support.incidence selected)) →
  Overlay.TriadicTwoChannelOverlay
    (Fine.structuredTriadicAtomsFromClassified pairing hh classified)
twoChannelOverlayFromClassified system pairing hh [] valuesExact =
  Overlay.overlay[]
twoChannelOverlayFromClassified system pairing hh
    (classified ∷ rest) valuesExact =
  let
    incidence = Support.incidence classified
    channels = channelsForClassified system classified
    valueExact = valuesExact classified
    sourceChannels = literalRationalTriadValueIsChannelTotal system incidence
    productExact :
      Shell.triadValue pairing incidence
      ≡ Channels.left0 channels * Channels.right0 channels
        + Channels.left1 channels * Channels.right1 channels
    productExact = trans valueExact sourceChannels
    tailExact = λ selected → valuesExact selected
  in
  Overlay.overlayTriadic2
    (Channels.left0 channels)
    (Channels.right0 channels)
    (Channels.left1 channels)
    (Channels.right1 channels)
    productExact
    (twoChannelOverlayFromClassified system pairing hh rest tailExact)

staticRationalTwoChannelOverlay :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode)
    (commutatorValue : Z3.FourierMode → ℚ)
    (hh : Fine.HHOwnerSelection) →
  Overlay.TriadicTwoChannelOverlay
    (Fine.structuredTriadicAtoms
      (staticRationalPhysicalPairing system output commutatorValue) hh)
staticRationalTwoChannelOverlay system output commutatorValue hh =
  twoChannelOverlayFromClassified
    system
    (staticRationalPhysicalPairing system output commutatorValue)
    hh
    (Support.classifiedPhysicalOutputFiber (Audit.cutoff system) output)
    (λ selected → refl)

staticRationalTwoChannelCauchy :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode)
    (commutatorValue : Z3.FourierMode → ℚ)
    (hh : Fine.HHOwnerSelection) →
  RationalL2.square
    (DASHI.Physics.Closure.NSTriadKNCriticalRemainderTriadicCauchyRound71Exact.triadicSignedSum
      (Fine.structuredTriadicAtoms
        (staticRationalPhysicalPairing system output commutatorValue) hh))
  RationalL2.≤
    (Overlay.twoChannelCharge
      (staticRationalTwoChannelOverlay system output commutatorValue hh))
    (Overlay.twoChannelEffectiveComplexity
      (staticRationalTwoChannelOverlay system output commutatorValue hh))
staticRationalTwoChannelCauchy system output commutatorValue hh =
  Overlay.twoChannelCauchy
    (staticRationalTwoChannelOverlay system output commutatorValue hh)

round75LiteralRationalTriadValueIsCanonicalTwoChannelProduct : Bool
round75LiteralRationalTriadValueIsCanonicalTwoChannelProduct = true

round75StaticRationalTwoChannelOverlayConstructedModuloHHSelection : Bool
round75StaticRationalTwoChannelOverlayConstructedModuloHHSelection = true

round75PhysicalRealImaginaryChannelsTransportedToRationalOverlay : Bool
round75PhysicalRealImaginaryChannelsTransportedToRationalOverlay = true

round75TimeDependentTwoChannelOverlayOnSelectedTrajectoryConstructed : Bool
round75TimeDependentTwoChannelOverlayOnSelectedTrajectoryConstructed = false

round75PhysicalRealImaginaryChannelsTransportedToRationalOverlayIsTrue :
  round75PhysicalRealImaginaryChannelsTransportedToRationalOverlay ≡ true
round75PhysicalRealImaginaryChannelsTransportedToRationalOverlayIsTrue = refl
