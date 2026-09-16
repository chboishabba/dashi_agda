module DASHI.Physics.Closure.NSTriadKNLowRemoteSpectralDatumRound98Exact where

------------------------------------------------------------------------
-- STRICT B-PHASE S2b2c2b / LITERAL LOW-REMOTE R98 SPECTRAL DATUM
--
-- The preceding #957 owners paid the exact three-region packet geometry and
-- transported the two-shell integer frequency gap onto the SAME rational
-- `C3.normSquared` carrier used by the literal viscous term.
--
-- This file performs the remaining finite packet lift.  For j = suc K:
--
--   low    : shellIndex < j
--   remote : shellIndex >= j+1
--
-- and, assuming only the physical viscosity premise 0 <= nu, it constructs the
-- actual R98 `SpectralCrossDissipationDatum` from the literal packet energies
-- and literal R407 viscous packet dissipations.
--
-- R98 uses half-energy
--
--   E_P = (1/2) sum_P |u_k|^2
--
-- while R407 contributes
--
--   D_P = nu sum_P |k|^2 |u_k|^2.
--
-- Therefore the spectral rates are exactly
--
--   lambda_low    = 2 nu * omega_low,
--   lambda_remote = 2 nu * omega_remote.
--
-- This is ordinary finite ordered algebra.  It does NOT consume the later S4
-- retained-viscosity condition `0 < 2 nu - a`, and it does NOT pay the collar
-- or the final integrated S2b2 inequality.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_; _<_ ; z≤n; s≤s)
import Data.Nat.Properties as Nat
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3EuclideanSelfPairing as Self
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as Euclidean
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as R30
import DASHI.Physics.Closure.NSTriadKNCanonicalLiteralProjectedODERound407Exact as R407
import DASHI.Physics.Closure.NSTriadKNPhysicalPacketBoundaryFluxLogReserveRound98Exact as Packet
import DASHI.Physics.Closure.NSTriadKNOffPacketRatioBoundaryFluxCoerciveRound98Exact as Ratio
import DASHI.Physics.Closure.NSTriadKNOffPacketSpectralCrossDissipationRound98Exact as Spectral
import DASHI.Physics.Closure.NSTriadKNLiteralUpperShellPacketSelectorExact as Upper
import DASHI.Physics.Closure.NSTriadKNLowCollarRemotePacketSplitExact as Split
import DASHI.Physics.Closure.NSTriadKNRationalIntegerEmbeddingModeNormScaleExact as Scale
import DASHI.Physics.Closure.NSTriadKNDyadicEuclideanShellMarginRound88Exact as R88
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNF4ProjectedOutputPairingRound39Exact as Pairing

F : C3.RealField _
F = Rational.rationalRealField

two : ℚ
two = 1ℚ + 1ℚ

------------------------------------------------------------------------
-- Literal modal mass and positivity.
------------------------------------------------------------------------

modalMass : C3.Complex3 F → ℚ
modalMass = Euclidean.complex3NormSquared

complexModulusSquaredNonnegative :
  (z : C3.Complex F) → 0ℚ ≤ Euclidean.complexModulusSquared z
complexModulusSquaredNonnegative (C3.complex real imaginary) =
  Rational.addNonnegative
    (Rational.squareNonnegative real)
    (Rational.squareNonnegative imaginary)

modalMassNonnegative :
  (v : C3.Complex3 F) → 0ℚ ≤ modalMass v
modalMassNonnegative (C3.complex3 x y z) =
  Rational.addNonnegative
    (Rational.addNonnegative
      (complexModulusSquaredNonnegative x)
      (complexModulusSquaredNonnegative y))
    (complexModulusSquaredNonnegative z)

selfPowerIsModalMass :
  (v : C3.Complex3 F) →
  Pairing.realHermitianPower v v ≡ modalMass v
selfPowerIsModalMass = Self.complex3SelfPairingRealPartIsNormSquared

selectedSelfSumNonnegative :
  (selected : Z3.FourierMode → Bool) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (modes : List Z3.FourierMode) →
  0ℚ ≤ Packet.sumSelectedPairing selected velocity velocity modes
selectedSelfSumNonnegative selected velocity [] = ℚP.≤-refl
selectedSelfSumNonnegative selected velocity (mode ∷ rest)
  with selected mode
... | false =
  subst
    (λ value → 0ℚ ≤ value)
    (sym (ℚP.+-identityˡ
      (Packet.sumSelectedPairing selected velocity velocity rest)))
    (selectedSelfSumNonnegative selected velocity rest)
... | true =
  Rational.addNonnegative
    (subst
      (λ value → 0ℚ ≤ value)
      (sym (selfPowerIsModalMass (velocity mode)))
      (modalMassNonnegative (velocity mode)))
    (selectedSelfSumNonnegative selected velocity rest)

oneHalfNonnegative : 0ℚ ≤ Ratio.oneHalf
oneHalfNonnegative = ℚP.nonNegative⁻¹ Ratio.oneHalf

literalSelectedEnergyNonnegative :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (selected : Z3.FourierMode → Bool) →
  0ℚ ≤ Ratio.literalSelectedEnergy system selected
literalSelectedEnergyNonnegative system selected =
  let
    massNN = selectedSelfSumNonnegative selected
      (Audit.velocity system)
      (Cube.cutoffModes (Audit.cutoff system))
    instance
      halfNN = nonNegative oneHalfNonnegative
      sumNN = nonNegative massNN
      prodNN = ℚP.nonNeg*nonNeg⇒nonNeg
        Ratio.oneHalf
        (Packet.sumSelectedPairing selected
          (Audit.velocity system) (Audit.velocity system)
          (Cube.cutoffModes (Audit.cutoff system)))
  in ℚP.nonNegative⁻¹ _

------------------------------------------------------------------------
-- Viscous selected sums are nu |k|^2 times modal mass.
------------------------------------------------------------------------

realPowerScaleRightSelf :
  (scalar : ℚ) (v : C3.Complex3 F) →
  Pairing.realHermitianPower v
      (C3.complex3Scale (C3.realEmbed F scalar) v)
  ≡ scalar * Pairing.realHermitianPower v v
realPowerScaleRightSelf scalar
    (C3.complex3
      (C3.complex xr xi) (C3.complex yr yi) (C3.complex zr zi)) =
  solve (scalar ∷ xr ∷ xi ∷ yr ∷ yi ∷ zr ∷ zi ∷ [])

selectedViscousTermMeaning :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (selected : Z3.FourierMode → Bool) →
  (mode : Z3.FourierMode) →
  Packet.selectedPairing selected
      (Audit.velocity (R30.finiteSystem physical))
      (R407.positiveViscousCoefficient physical) mode
  ≡
  (R30.viscosity physical
    * C3.normSquared (R30.physicalInverseSquare physical) mode)
  * Packet.selectedPairing selected
      (Audit.velocity (R30.finiteSystem physical))
      (Audit.velocity (R30.finiteSystem physical)) mode
selectedViscousTermMeaning physical selected mode with selected mode
... | false = solve []
... | true =
  realPowerScaleRightSelf
    (R30.viscosity physical
      * C3.normSquared (R30.physicalInverseSquare physical) mode)
    (Audit.velocity (R30.finiteSystem physical) mode)

------------------------------------------------------------------------
-- Generic finite selected packet order lift.
------------------------------------------------------------------------

selectedDissipationUpper :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (selected : Z3.FourierMode → Bool) →
  (ceiling : ℚ) →
  0ℚ ≤ R30.viscosity physical →
  ((mode : Z3.FourierMode) → selected mode ≡ true →
    C3.normSquared (R30.physicalInverseSquare physical) mode ≤ ceiling) →
  (modes : List Z3.FourierMode) →
  Packet.sumSelectedPairing selected
      (Audit.velocity (R30.finiteSystem physical))
      (R407.positiveViscousCoefficient physical) modes
  ≤
  (R30.viscosity physical * ceiling)
    * Packet.sumSelectedPairing selected
        (Audit.velocity (R30.finiteSystem physical))
        (Audit.velocity (R30.finiteSystem physical)) modes
selectedDissipationUpper physical selected ceiling nuNN pointwise [] = ℚP.≤-refl
selectedDissipationUpper physical selected ceiling nuNN pointwise
    (mode ∷ rest) with selected mode
... | false =
  let tail = selectedDissipationUpper
        physical selected ceiling nuNN pointwise rest
  in
  subst
    (λ left → left ≤
      (R30.viscosity physical * ceiling)
        * Packet.sumSelectedPairing selected
            (Audit.velocity (R30.finiteSystem physical))
            (Audit.velocity (R30.finiteSystem physical)) (mode ∷ rest))
    (sym (ℚP.+-identityˡ _))
    (subst
      (λ right →
        Packet.sumSelectedPairing selected
          (Audit.velocity (R30.finiteSystem physical))
          (R407.positiveViscousCoefficient physical) rest ≤ right)
      (sym
        (cong ((R30.viscosity physical * ceiling) *_)
          (ℚP.+-identityˡ
            (Packet.sumSelectedPairing selected
              (Audit.velocity (R30.finiteSystem physical))
              (Audit.velocity (R30.finiteSystem physical)) rest))))
      tail)
... | true =
  let
    u = Audit.velocity (R30.finiteSystem physical) mode
    mass = Pairing.realHermitianPower u u
    massNN : 0ℚ ≤ mass
    massNN = subst
      (λ value → 0ℚ ≤ value)
      (sym (selfPowerIsModalMass u))
      (modalMassNonnegative u)
    freq = C3.normSquared (R30.physicalInverseSquare physical) mode
    freq≤ = pointwise mode refl
    nuFreq≤ :
      R30.viscosity physical * freq
      ≤ R30.viscosity physical * ceiling
    nuFreq≤ =
      let instance nNN = nonNegative nuNN
      in ℚP.*-monoˡ-≤-nonNeg (R30.viscosity physical) freq≤
    head≤ :
      (R30.viscosity physical * freq) * mass
      ≤ (R30.viscosity physical * ceiling) * mass
    head≤ =
      let instance mNN = nonNegative massNN
      in ℚP.*-monoʳ-≤-nonNeg mass nuFreq≤
    tail≤ = selectedDissipationUpper
      physical selected ceiling nuNN pointwise rest
    added = ℚP.+-mono-≤ head≤ tail≤
    rhsDistrib :
      (R30.viscosity physical * ceiling) *
        (mass + Packet.sumSelectedPairing selected
          (Audit.velocity (R30.finiteSystem physical))
          (Audit.velocity (R30.finiteSystem physical)) rest)
      ≡
      (R30.viscosity physical * ceiling) * mass
      + (R30.viscosity physical * ceiling) *
        Packet.sumSelectedPairing selected
          (Audit.velocity (R30.finiteSystem physical))
          (Audit.velocity (R30.finiteSystem physical)) rest
    rhsDistrib = solve
      ( R30.viscosity physical ∷ ceiling ∷ mass
      ∷ Packet.sumSelectedPairing selected
          (Audit.velocity (R30.finiteSystem physical))
          (Audit.velocity (R30.finiteSystem physical)) rest ∷ [])
  in
  rewrite selectedViscousTermMeaning physical selected mode =
    subst
      (λ right →
        (R30.viscosity physical * freq) * mass
        + Packet.sumSelectedPairing selected
            (Audit.velocity (R30.finiteSystem physical))
            (R407.positiveViscousCoefficient physical) rest
        ≤ right)
      (sym rhsDistrib)
      added

selectedDissipationLower :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (selected : Z3.FourierMode → Bool) →
  (floor : ℚ) →
  0ℚ ≤ R30.viscosity physical →
  ((mode : Z3.FourierMode) → selected mode ≡ true →
    floor ≤ C3.normSquared (R30.physicalInverseSquare physical) mode) →
  (modes : List Z3.FourierMode) →
  (R30.viscosity physical * floor)
    * Packet.sumSelectedPairing selected
        (Audit.velocity (R30.finiteSystem physical))
        (Audit.velocity (R30.finiteSystem physical)) modes
  ≤
  Packet.sumSelectedPairing selected
      (Audit.velocity (R30.finiteSystem physical))
      (R407.positiveViscousCoefficient physical) modes
selectedDissipationLower physical selected floor nuNN pointwise [] = ℚP.≤-refl
selectedDissipationLower physical selected floor nuNN pointwise
    (mode ∷ rest) with selected mode
... | false =
  let tail = selectedDissipationLower
        physical selected floor nuNN pointwise rest
  in
  subst
    (λ left → left ≤
      Packet.sumSelectedPairing selected
        (Audit.velocity (R30.finiteSystem physical))
        (R407.positiveViscousCoefficient physical) (mode ∷ rest))
    (cong ((R30.viscosity physical * floor) *_)
      (ℚP.+-identityˡ
        (Packet.sumSelectedPairing selected
          (Audit.velocity (R30.finiteSystem physical))
          (Audit.velocity (R30.finiteSystem physical)) rest)))
    (subst
      (λ right →
        (R30.viscosity physical * floor) *
          Packet.sumSelectedPairing selected
            (Audit.velocity (R30.finiteSystem physical))
            (Audit.velocity (R30.finiteSystem physical)) rest ≤ right)
      (sym (ℚP.+-identityˡ _))
      tail)
... | true =
  let
    u = Audit.velocity (R30.finiteSystem physical) mode
    mass = Pairing.realHermitianPower u u
    massNN : 0ℚ ≤ mass
    massNN = subst
      (λ value → 0ℚ ≤ value)
      (sym (selfPowerIsModalMass u))
      (modalMassNonnegative u)
    freq = C3.normSquared (R30.physicalInverseSquare physical) mode
    floor≤freq = pointwise mode refl
    nuFloor≤ :
      R30.viscosity physical * floor
      ≤ R30.viscosity physical * freq
    nuFloor≤ =
      let instance nNN = nonNegative nuNN
      in ℚP.*-monoˡ-≤-nonNeg (R30.viscosity physical) floor≤freq
    head≤ :
      (R30.viscosity physical * floor) * mass
      ≤ (R30.viscosity physical * freq) * mass
    head≤ =
      let instance mNN = nonNegative massNN
      in ℚP.*-monoʳ-≤-nonNeg mass nuFloor≤
    tail≤ = selectedDissipationLower
      physical selected floor nuNN pointwise rest
    added = ℚP.+-mono-≤ head≤ tail≤
    lhsDistrib :
      (R30.viscosity physical * floor) *
        (mass + Packet.sumSelectedPairing selected
          (Audit.velocity (R30.finiteSystem physical))
          (Audit.velocity (R30.finiteSystem physical)) rest)
      ≡
      (R30.viscosity physical * floor) * mass
      + (R30.viscosity physical * floor) *
        Packet.sumSelectedPairing selected
          (Audit.velocity (R30.finiteSystem physical))
          (Audit.velocity (R30.finiteSystem physical)) rest
    lhsDistrib = solve
      ( R30.viscosity physical ∷ floor ∷ mass
      ∷ Packet.sumSelectedPairing selected
          (Audit.velocity (R30.finiteSystem physical))
          (Audit.velocity (R30.finiteSystem physical)) rest ∷ [])
  in
  rewrite selectedViscousTermMeaning physical selected mode =
    subst
      (λ left → left ≤
        (R30.viscosity physical * freq) * mass
        + Packet.sumSelectedPairing selected
            (Audit.velocity (R30.finiteSystem physical))
            (R407.positiveViscousCoefficient physical) rest)
      lhsDistrib
      added

------------------------------------------------------------------------
-- Shell-selector facts for the literal low/remote regions.
------------------------------------------------------------------------

lowSelectedImpliesShellBelow :
  (K : Nat) (mode : Z3.FourierMode) →
  Split.lowPacket (suc K) mode ≡ true →
  Shell.shellIndex mode < suc K
lowSelectedImpliesShellBelow K mode selectedTrue
  with Output.modeEqual mode Z3.zeroMode
     | suc K Nat.≤? Shell.shellIndex mode
... | true | decision =
  subst
    (λ chosen → Shell.shellIndex chosen < suc K)
    (Output.modeEqualSound refl)
    (s≤s z≤n)
... | false | yes threshold≤ = Output.falseNotTrue selectedTrue
... | false | no thresholdNot≤ = Nat.≰⇒> thresholdNot≤

remoteSelectedImpliesShellAbove :
  (K : Nat) (mode : Z3.FourierMode) →
  Split.remotePacket (suc K) mode ≡ true →
  suc (suc K) ≤ Shell.shellIndex mode
remoteSelectedImpliesShellAbove K mode selectedTrue
  with Output.modeEqual mode Z3.zeroMode
     | suc (suc K) Nat.≤? Shell.shellIndex mode
... | true | decision = Output.falseNotTrue selectedTrue
... | false | yes threshold≤ = threshold≤
... | false | no thresholdNot≤ = Output.falseNotTrue selectedTrue

------------------------------------------------------------------------
-- Literal low/remote datum and coercive consequence.
------------------------------------------------------------------------

lowFrequency : C3.IntegerEmbedding F → Nat → ℚ
lowFrequency E K =
  Scale.scaledNatFrequency E (3 * R88.natSquare (Shell.pow2 K))

remoteFrequency : C3.IntegerEmbedding F → Nat → ℚ
remoteFrequency E K =
  Scale.scaledNatFrequency E (4 * R88.natSquare (Shell.pow2 K))

spectralRate : ℚ → ℚ → ℚ
spectralRate nu frequency = two * nu * frequency

selectedDissipationUpperAsEnergy :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (selected : Z3.FourierMode → Bool) →
  (ceiling : ℚ) →
  0ℚ ≤ R30.viscosity physical →
  ((mode : Z3.FourierMode) → selected mode ≡ true →
    C3.normSquared (R30.physicalInverseSquare physical) mode ≤ ceiling) →
  Packet.literalPacketDissipation
      (R30.finiteSystem physical)
      (R407.canonicalLiteralProjectedEquation physical) selected
  ≤ spectralRate (R30.viscosity physical) ceiling
      * Ratio.literalSelectedEnergy (R30.finiteSystem physical) selected
selectedDissipationUpperAsEnergy physical selected ceiling nuNN pointwise =
  let
    raw = selectedDissipationUpper physical selected ceiling nuNN pointwise
      (Cube.cutoffModes (Audit.cutoff (R30.finiteSystem physical)))
    mass = Packet.sumSelectedPairing selected
      (Audit.velocity (R30.finiteSystem physical))
      (Audit.velocity (R30.finiteSystem physical))
      (Cube.cutoffModes (Audit.cutoff (R30.finiteSystem physical)))
    normalized :
      spectralRate (R30.viscosity physical) ceiling * (Ratio.oneHalf * mass)
      ≡ (R30.viscosity physical * ceiling) * mass
    normalized = solve (R30.viscosity physical ∷ ceiling ∷ mass ∷ [])
  in
  subst
    (λ right →
      Packet.literalPacketDissipation
        (R30.finiteSystem physical)
        (R407.canonicalLiteralProjectedEquation physical) selected ≤ right)
    (sym normalized)
    raw

selectedDissipationLowerAsEnergy :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (selected : Z3.FourierMode → Bool) →
  (floor : ℚ) →
  0ℚ ≤ R30.viscosity physical →
  ((mode : Z3.FourierMode) → selected mode ≡ true →
    floor ≤ C3.normSquared (R30.physicalInverseSquare physical) mode) →
  spectralRate (R30.viscosity physical) floor
      * Ratio.literalSelectedEnergy (R30.finiteSystem physical) selected
  ≤ Packet.literalPacketDissipation
      (R30.finiteSystem physical)
      (R407.canonicalLiteralProjectedEquation physical) selected
selectedDissipationLowerAsEnergy physical selected floor nuNN pointwise =
  let
    raw = selectedDissipationLower physical selected floor nuNN pointwise
      (Cube.cutoffModes (Audit.cutoff (R30.finiteSystem physical)))
    mass = Packet.sumSelectedPairing selected
      (Audit.velocity (R30.finiteSystem physical))
      (Audit.velocity (R30.finiteSystem physical))
      (Cube.cutoffModes (Audit.cutoff (R30.finiteSystem physical)))
    normalized :
      spectralRate (R30.viscosity physical) floor * (Ratio.oneHalf * mass)
      ≡ (R30.viscosity physical * floor) * mass
    normalized = solve (R30.viscosity physical ∷ floor ∷ mass ∷ [])
  in
  subst
    (λ left → left ≤
      Packet.literalPacketDissipation
        (R30.finiteSystem physical)
        (R407.canonicalLiteralProjectedEquation physical) selected)
    normalized
    raw

frequencyNonnegative :
  (E : C3.IntegerEmbedding F) (n : Nat) →
  0ℚ ≤ Scale.scaledNatFrequency E n
frequencyNonnegative E n =
  let
    unitNN = Scale.unitSquareNonnegative E
    natNN = Scale.natAsRationalNonnegative n
    instance
      uNN = nonNegative unitNN
      nNN = nonNegative natNN
      productNN = ℚP.nonNeg*nonNeg⇒nonNeg
        (Scale.unitSquare E) (Scale.modeNatNormAsRational (Z3.mode (+ 0) (+ 0) (+ 0)))
  in
  let instance
      uNN2 = nonNegative unitNN
      nNN2 = nonNegative natNN
      productNN2 = ℚP.nonNeg*nonNeg⇒nonNeg
        (Scale.unitSquare E) (Scale.S0.natAsRational n)
  in ℚP.nonNegative⁻¹ _

spectralRateNonnegative :
  ∀ nu frequency → 0ℚ ≤ nu → 0ℚ ≤ frequency →
  0ℚ ≤ spectralRate nu frequency
spectralRateNonnegative nu frequency nuNN frequencyNN =
  let
    twoNN : 0ℚ ≤ two
    twoNN = Rational.addNonnegative ℚP.≤-refl (ℚP.nonNegative⁻¹ 1ℚ)
    firstNN : 0ℚ ≤ two * nu
    firstNN =
      let instance a = nonNegative twoNN; b = nonNegative nuNN
      in ℚP.nonNegative⁻¹ _
  in
  let instance a = nonNegative firstNN; b = nonNegative frequencyNN
  in ℚP.nonNegative⁻¹ _

buildLowRemoteSpectralDatum :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (K : Nat) →
  0ℚ ≤ R30.viscosity physical →
  Spectral.SpectralCrossDissipationDatum
buildLowRemoteSpectralDatum physical K nuNN = record
  { Spectral.packetEnergy =
      Ratio.literalSelectedEnergy system low
  ; Spectral.offPacketEnergy =
      Ratio.literalSelectedEnergy system remote
  ; Spectral.packetDissipation =
      Packet.literalPacketDissipation system ode low
  ; Spectral.offPacketDissipation =
      Packet.literalPacketDissipation system ode remote
  ; Spectral.packetFrequencyCeiling = spectralRate nu lowFreq
  ; Spectral.offPacketFrequencyFloor = spectralRate nu remoteFreq
  ; Spectral.packetEnergyNonnegative =
      literalSelectedEnergyNonnegative system low
  ; Spectral.offPacketEnergyNonnegative =
      literalSelectedEnergyNonnegative system remote
  ; Spectral.packetFrequencyCeilingNonnegative =
      spectralRateNonnegative nu lowFreq nuNN (frequencyNonnegative E _)
  ; Spectral.offPacketFrequencyFloorNonnegative =
      spectralRateNonnegative nu remoteFreq nuNN (frequencyNonnegative E _)
  ; Spectral.packetDissipationUpper =
      selectedDissipationUpperAsEnergy physical low lowFreq nuNN
        (λ mode hit → Scale.liveLowFrequencyCeiling E I
          (lowSelectedImpliesShellBelow K mode hit))
  ; Spectral.offPacketDissipationLower =
      selectedDissipationLowerAsEnergy physical remote remoteFreq nuNN
        (λ mode hit → Scale.liveRemoteFrequencyFloor E I
          (remoteSelectedImpliesShellAbove K mode hit))
  }
  where
  system = R30.finiteSystem physical
  E = R30.physicalEmbedding physical
  I = R30.physicalInverseSquare physical
  ode = R407.canonicalLiteralProjectedEquation physical
  nu = R30.viscosity physical
  low = Split.lowPacket (suc K)
  remote = Split.remotePacket (suc K)
  lowFreq = lowFrequency E K
  remoteFreq = remoteFrequency E K

lowRateBelowRemoteRate :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (K : Nat) →
  0ℚ ≤ R30.viscosity physical →
  spectralRate (R30.viscosity physical) (lowFrequency (R30.physicalEmbedding physical) K)
  ≤ spectralRate (R30.viscosity physical) (remoteFrequency (R30.physicalEmbedding physical) K)
lowRateBelowRemoteRate physical K nuNN =
  let
    base = Scale.liveLowCeilingBelowRemoteFloor
      (R30.physicalEmbedding physical) K
    twoNN : 0ℚ ≤ two
    twoNN = Rational.addNonnegative (ℚP.nonNegative⁻¹ 1ℚ) (ℚP.nonNegative⁻¹ 1ℚ)
    scaleNN : 0ℚ ≤ two * R30.viscosity physical
    scaleNN =
      let instance a = nonNegative twoNN; b = nonNegative nuNN
      in ℚP.nonNegative⁻¹ _
    instance sNN = nonNegative scaleNN
  in ℚP.*-monoˡ-≤-nonNeg (two * R30.viscosity physical) base

lowRemotePositiveSpectralGap :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (K : Nat) →
  (nuNN : 0ℚ ≤ R30.viscosity physical) →
  Spectral.PositiveSpectralGap
    (buildLowRemoteSpectralDatum physical K nuNN)
lowRemotePositiveSpectralGap physical K nuNN = record
  { Spectral.gapPositive = gapNN }
  where
  lowRate = spectralRate (R30.viscosity physical)
    (lowFrequency (R30.physicalEmbedding physical) K)
  remoteRate = spectralRate (R30.viscosity physical)
    (remoteFrequency (R30.physicalEmbedding physical) K)
  order = lowRateBelowRemoteRate physical K nuNN
  shifted = ℚP.+-monoʳ-≤ (- lowRate) order
  gapNN : 0ℚ ≤ remoteRate - lowRate
  gapNN =
    subst
      (λ left → left ≤ remoteRate - lowRate)
      (solve (lowRate ∷ []))
      (subst
        (λ right → lowRate + (- lowRate) ≤ right)
        (solve (remoteRate ∷ lowRate ∷ []))
        shifted)

remoteSpectralCrossTermNonpositive :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (K : Nat) →
  (nuNN : 0ℚ ≤ R30.viscosity physical) →
  let D = buildLowRemoteSpectralDatum physical K nuNN
  in
  Spectral.offPacketEnergy D * Spectral.packetDissipation D
    - Spectral.offPacketDissipation D * Spectral.packetEnergy D
  ≤ 0ℚ
remoteSpectralCrossTermNonpositive physical K nuNN =
  Spectral.spectralCrossDissipationNonpositive
    (buildLowRemoteSpectralDatum physical K nuNN)
    (lowRemotePositiveSpectralGap physical K nuNN)

------------------------------------------------------------------------
-- Status / firewalls.
------------------------------------------------------------------------

literalLowRemoteSpectralDatumConstructed : Bool
literalLowRemoteSpectralDatumConstructed = true

twoNuNormalizationFirewallClosed : Bool
twoNuNormalizationFirewallClosed = true

remoteSpectralCrossCoercivityConstructed : Bool
remoteSpectralCrossCoercivityConstructed = true

collarRemainsIndependent : Bool
collarRemainsIndependent = true

literalLowRemoteSpectralDatumConstructedIsTrue :
  literalLowRemoteSpectralDatumConstructed ≡ true
literalLowRemoteSpectralDatumConstructedIsTrue = refl

twoNuNormalizationFirewallClosedIsTrue :
  twoNuNormalizationFirewallClosed ≡ true
twoNuNormalizationFirewallClosedIsTrue = refl

remoteSpectralCrossCoercivityConstructedIsTrue :
  remoteSpectralCrossCoercivityConstructed ≡ true
remoteSpectralCrossCoercivityConstructedIsTrue = refl

collarRemainsIndependentIsTrue : collarRemainsIndependent ≡ true
collarRemainsIndependentIsTrue = refl
