{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650LowCollarRemoteCrossReductionRound655Exact where

------------------------------------------------------------------------
-- ROUND655 / LOW-COMPLEMENT CROSS TERM REDUCES TO COLLAR
--
-- R654 keeps two distinct facts separate:
--
--   * the literal two-shell low/remote spectral cross is coercive;
--   * that fact does not directly pay the remote boundary flux.
--
-- There is nevertheless a useful exact consequence inside R98's off-packet
-- ratio identity.  Relative to the LOW selector, the literal complement is
-- exactly
--
--     collar disjoint-union remote.
--
-- Hence both selected half-energy and selected viscous dissipation split:
--
--     E_off(low) = E_collar + E_remote,
--     D_off(low) = D_collar + D_remote.
--
-- Therefore the full off-packet spectral cross
--
--     E_off D_low - D_off E_low
--
-- is exactly
--
--     (E_collar D_low - D_collar E_low)
--       + (E_remote D_low - D_remote E_low).
--
-- R654/R98 already prove the remote term <= 0 on the genuine two-shell
-- low/remote split.  Consequently
--
--     full off-packet cross <= collar cross.
--
-- This is an actual analytic reduction, not a boundary-flux estimate.  It
-- deletes the remote spectral-cross contribution from the hard ratio dynamics
-- while preserving the firewall that remote flux itself remains unpaid.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥-elim)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNF4ProjectedOutputPairingRound39Exact as Pairing
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as R30
import DASHI.Physics.Closure.NSTriadKNCanonicalLiteralProjectedODERound407Exact as R407
import DASHI.Physics.Closure.NSTriadKNPhysicalPacketBoundaryFluxLogReserveRound98Exact as Packet
import DASHI.Physics.Closure.NSTriadKNOffPacketRatioBoundaryFluxCoerciveRound98Exact as Ratio
import DASHI.Physics.Closure.NSTriadKNLiteralUpperShellPacketSelectorExact as Upper
import DASHI.Physics.Closure.NSTriadKNUpperShellCollarRemoteSplitExact as Collar
import DASHI.Physics.Closure.NSTriadKNLowCollarRemotePacketSplitExact as Split
import DASHI.Physics.Closure.NSTriadKNLowRemoteSpectralDatumRound98Exact as Remote
import DASHI.Physics.Closure.NSTriadKNOffPacketSpectralCrossDissipationRound98Exact as Spectral

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- Generic selected-pairing partition on the literal low/collar/remote selectors.
------------------------------------------------------------------------

selectedPairingThreeRegion :
  (threshold : Nat) →
  (test value : Z3.FourierMode → C3.Complex3 F) →
  (mode : Z3.FourierMode) →
  Packet.selectedPairing (Split.lowPacket threshold) test value mode
    + Packet.selectedPairing (Split.collarPacket threshold) test value mode
    + Packet.selectedPairing (Split.remotePacket threshold) test value mode
  ≡ Packet.selectedPairing Ratio.allSelected test value mode
selectedPairingThreeRegion threshold test value mode
  with Upper.upperShellPacket threshold mode in current
     | Upper.upperShellPacket (suc threshold) mode in successor
... | false | false = refl
... | true | false = solve
  (Pairing.realHermitianPower
    (test mode) (value mode) ∷ [])
... | true | true = solve
  (Pairing.realHermitianPower
    (test mode) (value mode) ∷ [])
... | false | true =
  ⊥-elim
    (Output.falseNotTrue
      (trans (sym current)
        (Collar.upperSuccessorTrueImpliesUpperTrue
          threshold mode successor)))

sumSelectedPairingThreeRegion :
  (threshold : Nat) →
  (test value : Z3.FourierMode → C3.Complex3 F) →
  (modes : List Z3.FourierMode) →
  Packet.sumSelectedPairing (Split.lowPacket threshold) test value modes
    + Packet.sumSelectedPairing (Split.collarPacket threshold) test value modes
    + Packet.sumSelectedPairing (Split.remotePacket threshold) test value modes
  ≡ Packet.sumSelectedPairing Ratio.allSelected test value modes
sumSelectedPairingThreeRegion threshold test value [] = refl
sumSelectedPairingThreeRegion threshold test value (mode ∷ rest)
  rewrite selectedPairingThreeRegion threshold test value mode
        | sumSelectedPairingThreeRegion threshold test value rest =
  solve
    ( Packet.selectedPairing Ratio.allSelected test value mode
    ∷ Packet.sumSelectedPairing Ratio.allSelected test value rest
    ∷ [])

------------------------------------------------------------------------
-- Literal energy / dissipation partition.
------------------------------------------------------------------------

literalPacketEnergy :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  (Z3.FourierMode → Bool) → ℚ
literalPacketEnergy = Ratio.literalSelectedEnergy

literalPacketDissipation :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (Z3.FourierMode → Bool) → ℚ
literalPacketDissipation physical =
  Packet.literalPacketDissipation
    (R30.finiteSystem physical)
    (R407.canonicalLiteralProjectedEquation physical)

literalEnergyThreeRegion :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (threshold : Nat) →
  let system = R30.finiteSystem physical
  in
  literalPacketEnergy system (Split.lowPacket threshold)
    + literalPacketEnergy system (Split.collarPacket threshold)
    + literalPacketEnergy system (Split.remotePacket threshold)
  ≡ Ratio.literalTotalEnergy system
literalEnergyThreeRegion physical threshold =
  let
    system = R30.finiteSystem physical
    velocity = Audit.velocity system
    modes = Cube.cutoffModes (Audit.cutoff system)
    raw = sumSelectedPairingThreeRegion
      threshold velocity velocity modes
  in
  trans
    (solve
      ( Ratio.oneHalf
      ∷ Packet.sumSelectedPairing (Split.lowPacket threshold)
          velocity velocity modes
      ∷ Packet.sumSelectedPairing (Split.collarPacket threshold)
          velocity velocity modes
      ∷ Packet.sumSelectedPairing (Split.remotePacket threshold)
          velocity velocity modes
      ∷ []))
    (cong (Ratio.oneHalf *_) raw)

literalDissipationThreeRegion :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (threshold : Nat) →
  literalPacketDissipation physical (Split.lowPacket threshold)
    + literalPacketDissipation physical (Split.collarPacket threshold)
    + literalPacketDissipation physical (Split.remotePacket threshold)
  ≡ Ratio.literalTotalDissipation
      (R30.finiteSystem physical)
      (R407.canonicalLiteralProjectedEquation physical)
literalDissipationThreeRegion physical threshold =
  let
    system = R30.finiteSystem physical
    ode = R407.canonicalLiteralProjectedEquation physical
    velocity = Audit.velocity system
    viscous = Audit.viscousTerm ode
    modes = Cube.cutoffModes (Audit.cutoff system)
  in
  sumSelectedPairingThreeRegion threshold velocity viscous modes

offPacketEnergyLowIsCollarPlusRemote :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (threshold : Nat) →
  let system = R30.finiteSystem physical
  in
  Ratio.literalOffPacketEnergy system (Split.lowPacket threshold)
  ≡
  literalPacketEnergy system (Split.collarPacket threshold)
    + literalPacketEnergy system (Split.remotePacket threshold)
offPacketEnergyLowIsCollarPlusRemote physical threshold =
  let
    system = R30.finiteSystem physical
    low = literalPacketEnergy system (Split.lowPacket threshold)
    collar = literalPacketEnergy system (Split.collarPacket threshold)
    remote = literalPacketEnergy system (Split.remotePacket threshold)
    total = Ratio.literalTotalEnergy system
    partition : low + collar + remote ≡ total
    partition = literalEnergyThreeRegion physical threshold
  in
  trans
    (cong (λ value → value - low) (sym partition))
    (solve (low ∷ collar ∷ remote ∷ []))

offPacketDissipationLowIsCollarPlusRemote :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (threshold : Nat) →
  let
    system = R30.finiteSystem physical
    ode = R407.canonicalLiteralProjectedEquation physical
  in
  Ratio.literalOffPacketDissipation system ode (Split.lowPacket threshold)
  ≡
  literalPacketDissipation physical (Split.collarPacket threshold)
    + literalPacketDissipation physical (Split.remotePacket threshold)
offPacketDissipationLowIsCollarPlusRemote physical threshold =
  let
    system = R30.finiteSystem physical
    ode = R407.canonicalLiteralProjectedEquation physical
    low = literalPacketDissipation physical (Split.lowPacket threshold)
    collar = literalPacketDissipation physical (Split.collarPacket threshold)
    remote = literalPacketDissipation physical (Split.remotePacket threshold)
    total = Ratio.literalTotalDissipation system ode
    partition : low + collar + remote ≡ total
    partition = literalDissipationThreeRegion physical threshold
  in
  trans
    (cong (λ value → value - low) (sym partition))
    (solve (low ∷ collar ∷ remote ∷ []))

------------------------------------------------------------------------
-- Cross-term reduction.
------------------------------------------------------------------------

spectralCross : ℚ → ℚ → ℚ → ℚ → ℚ
spectralCross offEnergy packetDissipation offDissipation packetEnergy =
  offEnergy * packetDissipation - offDissipation * packetEnergy

fullLowComplementCross :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  Nat → ℚ
fullLowComplementCross physical threshold =
  let
    system = R30.finiteSystem physical
    ode = R407.canonicalLiteralProjectedEquation physical
    low = Split.lowPacket threshold
  in
  spectralCross
    (Ratio.literalOffPacketEnergy system low)
    (literalPacketDissipation physical low)
    (Ratio.literalOffPacketDissipation system ode low)
    (literalPacketEnergy system low)

collarCross :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  Nat → ℚ
collarCross physical threshold =
  let system = R30.finiteSystem physical
  in
  spectralCross
    (literalPacketEnergy system (Split.collarPacket threshold))
    (literalPacketDissipation physical (Split.lowPacket threshold))
    (literalPacketDissipation physical (Split.collarPacket threshold))
    (literalPacketEnergy system (Split.lowPacket threshold))

remoteCross :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  Nat → ℚ
remoteCross physical threshold =
  let system = R30.finiteSystem physical
  in
  spectralCross
    (literalPacketEnergy system (Split.remotePacket threshold))
    (literalPacketDissipation physical (Split.lowPacket threshold))
    (literalPacketDissipation physical (Split.remotePacket threshold))
    (literalPacketEnergy system (Split.lowPacket threshold))

fullCrossIsCollarPlusRemote :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (threshold : Nat) →
  fullLowComplementCross physical threshold
  ≡ collarCross physical threshold + remoteCross physical threshold
fullCrossIsCollarPlusRemote physical threshold =
  let
    system = R30.finiteSystem physical
    ode = R407.canonicalLiteralProjectedEquation physical
    lowE = literalPacketEnergy system (Split.lowPacket threshold)
    collarE = literalPacketEnergy system (Split.collarPacket threshold)
    remoteE = literalPacketEnergy system (Split.remotePacket threshold)
    lowD = literalPacketDissipation physical (Split.lowPacket threshold)
    collarD = literalPacketDissipation physical (Split.collarPacket threshold)
    remoteD = literalPacketDissipation physical (Split.remotePacket threshold)
  in
  rewrite offPacketEnergyLowIsCollarPlusRemote physical threshold
        | offPacketDissipationLowIsCollarPlusRemote physical threshold =
    solve (lowE ∷ collarE ∷ remoteE ∷ lowD ∷ collarD ∷ remoteD ∷ [])

remoteCrossNonpositive :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (K : Nat) →
  (nuNN : 0ℚ ≤ R30.viscosity physical) →
  remoteCross physical (suc K) ≤ 0ℚ
remoteCrossNonpositive physical K nuNN =
  Remote.remoteSpectralCrossTermNonpositive physical K nuNN

fullCrossBelowCollarCross :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (K : Nat) →
  (nuNN : 0ℚ ≤ R30.viscosity physical) →
  fullLowComplementCross physical (suc K)
  ≤ collarCross physical (suc K)
fullCrossBelowCollarCross physical K nuNN =
  let
    remote≤0 = remoteCrossNonpositive physical K nuNN
    add =
      ℚP.+-mono-≤
        ℚP.≤-refl
        remote≤0
    normalized :
      collarCross physical (suc K) + 0ℚ
      ≡ collarCross physical (suc K)
    normalized = solve (collarCross physical (suc K) ∷ [])
  in
  subst
    (λ right → fullLowComplementCross physical (suc K) ≤ right)
    normalized
    (subst
      (λ left → left ≤ collarCross physical (suc K) + 0ℚ)
      (sym (fullCrossIsCollarPlusRemote physical (suc K)))
      add)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round655LiteralEnergyThreeRegionSplitClosed : Bool
round655LiteralEnergyThreeRegionSplitClosed = true

round655LiteralDissipationThreeRegionSplitClosed : Bool
round655LiteralDissipationThreeRegionSplitClosed = true

round655FullOffPacketCrossIsCollarPlusRemoteClosed : Bool
round655FullOffPacketCrossIsCollarPlusRemoteClosed = true

round655RemoteCrossDeletedBySpectralCoercivity : Bool
round655RemoteCrossDeletedBySpectralCoercivity = true

round655FullOffPacketCrossReducedToCollar : Bool
round655FullOffPacketCrossReducedToCollar = true

round655RemoteBoundaryFluxPaid : Bool
round655RemoteBoundaryFluxPaid = false

round655SignedCollarPaymentClosed : Bool
round655SignedCollarPaymentClosed = false

round655IntroducesNewClayLeaf : Bool
round655IntroducesNewClayLeaf = false

round655C2Closed : Bool
round655C2Closed = false

round655ClayPromotion : Bool
round655ClayPromotion = false

round655LiteralEnergyThreeRegionSplitClosedIsTrue :
  round655LiteralEnergyThreeRegionSplitClosed ≡ true
round655LiteralEnergyThreeRegionSplitClosedIsTrue = refl

round655LiteralDissipationThreeRegionSplitClosedIsTrue :
  round655LiteralDissipationThreeRegionSplitClosed ≡ true
round655LiteralDissipationThreeRegionSplitClosedIsTrue = refl

round655FullOffPacketCrossIsCollarPlusRemoteClosedIsTrue :
  round655FullOffPacketCrossIsCollarPlusRemoteClosed ≡ true
round655FullOffPacketCrossIsCollarPlusRemoteClosedIsTrue = refl

round655RemoteCrossDeletedBySpectralCoercivityIsTrue :
  round655RemoteCrossDeletedBySpectralCoercivity ≡ true
round655RemoteCrossDeletedBySpectralCoercivityIsTrue = refl

round655FullOffPacketCrossReducedToCollarIsTrue :
  round655FullOffPacketCrossReducedToCollar ≡ true
round655FullOffPacketCrossReducedToCollarIsTrue = refl

round655RemoteBoundaryFluxPaidIsFalse :
  round655RemoteBoundaryFluxPaid ≡ false
round655RemoteBoundaryFluxPaidIsFalse = refl

round655SignedCollarPaymentClosedIsFalse :
  round655SignedCollarPaymentClosed ≡ false
round655SignedCollarPaymentClosedIsFalse = refl

round655IntroducesNewClayLeafIsFalse :
  round655IntroducesNewClayLeaf ≡ false
round655IntroducesNewClayLeafIsFalse = refl

round655C2ClosedIsFalse :
  round655C2Closed ≡ false
round655C2ClosedIsFalse = refl

round655ClayPromotionIsFalse :
  round655ClayPromotion ≡ false
round655ClayPromotionIsFalse = refl
