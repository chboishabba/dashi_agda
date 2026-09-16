module DASHI.Physics.Closure.NSTriadKNLowCollarRemotePacketSplitExact where

------------------------------------------------------------------------
-- STRICT B-PHASE S2b2c0 / EXACT LOW-COLLAR-REMOTE PACKET SPLIT
--
-- The collar/remote split alone does NOT make the remote packet the Boolean
-- complement of a spectrally separated low packet.  The correct literal
-- geometry is three-region:
--
--   low    : shellIndex < j
--   collar : shellIndex = j
--   remote : shellIndex >= j+1
--
-- (with the existing R98 zero-mode convention inherited by the low selector).
--
-- This owner proves the exact normalized R98 boundary-flux identity
--
--   F_low + F_collar + F_remote = 0
--
-- by composing the already-proved complement antisymmetry
--
--   F_low = - F_{>=j}
--
-- with the exact collar/remote decomposition
--
--   F_{>=j} = F_collar + F_remote.
--
-- It intentionally does NOT construct the R98 SpectralCrossDissipationDatum
-- for low versus remote.  That requires new literal frequency/dissipation
-- bounds after removing the collar and remains a separate S2b2 analytic leaf.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Reality
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralUpperShellPacketSelectorExact as Upper
import DASHI.Physics.Closure.NSTriadKNPacketBoundaryFluxNormalizationRound98Exact as Norm
import DASHI.Physics.Closure.NSTriadKNPacketBoundaryFluxComplementRound98Exact as Complement
import DASHI.Physics.Closure.NSTriadKNUpperShellCollarRemoteSplitExact as Collar

F : C3.RealField _
F = Rational.rationalRealField

lowPacket : Nat → Z3.FourierMode → Bool
lowPacket = Complement.lowerShellPacket

collarPacket : Nat → Z3.FourierMode → Bool
collarPacket = Collar.collarShellPacket

remotePacket : Nat → Z3.FourierMode → Bool
remotePacket threshold = Upper.upperShellPacket (suc threshold)

threeRegionBoundaryFluxIdentity :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (threshold : Nat) →
  Reality.RealityCondition (Audit.velocity system) →
  Reality.DivergenceFreeCondition E (Audit.velocity system) →
  Norm.normalizedBoundaryTransfer
      E I (lowPacket threshold)
      (Audit.velocity system) (Audit.cutoff system)
    + Norm.normalizedBoundaryTransfer
      E I (collarPacket threshold)
      (Audit.velocity system) (Audit.cutoff system)
    + Norm.normalizedBoundaryTransfer
      E I (remotePacket threshold)
      (Audit.velocity system) (Audit.cutoff system)
  ≡ 0ℚ
threeRegionBoundaryFluxIdentity
    {E} {I} system threshold reality divergenceFree =
  let
    lowOpposition =
      Complement.lowerShellBoundaryFluxIsNegativeUpperShellFlux
        E I threshold (Audit.velocity system)
        reality divergenceFree (Audit.cutoff system)

    upperSplit =
      Collar.normalizedBoundaryFluxCollarRemoteSplit
        system threshold reality divergenceFree

    collarFlux =
      Norm.normalizedBoundaryTransfer
        E I (collarPacket threshold)
        (Audit.velocity system) (Audit.cutoff system)

    remoteFlux =
      Norm.normalizedBoundaryTransfer
        E I (remotePacket threshold)
        (Audit.velocity system) (Audit.cutoff system)
  in
  rewrite lowOpposition | upperSplit =
    solve (collarFlux ∷ remoteFlux ∷ [])

------------------------------------------------------------------------
-- Status / firewall.
------------------------------------------------------------------------

threeRegionBoundaryFluxIdentityClosed : Bool
threeRegionBoundaryFluxIdentityClosed = true

-- Explicit design firewall: the remote packet is not treated as the Boolean
-- complement of low.  The collar is a distinct third region.
remoteIsNotUsedAsBooleanComplement : Bool
remoteIsNotUsedAsBooleanComplement = true

-- Still unpaid: construct literal low/remote energies and dissipations with
-- the strict frequency separation required by R98's coercive datum.
literalLowRemoteSpectralDatumConstructed : Bool
literalLowRemoteSpectralDatumConstructed = false

threeRegionBoundaryFluxIdentityClosedIsTrue :
  threeRegionBoundaryFluxIdentityClosed ≡ true
threeRegionBoundaryFluxIdentityClosedIsTrue = refl

remoteIsNotUsedAsBooleanComplementIsTrue :
  remoteIsNotUsedAsBooleanComplement ≡ true
remoteIsNotUsedAsBooleanComplementIsTrue = refl

literalLowRemoteSpectralDatumConstructedIsFalse :
  literalLowRemoteSpectralDatumConstructed ≡ false
literalLowRemoteSpectralDatumConstructedIsFalse = refl
