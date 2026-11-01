module DASHI.Physics.Closure.NSTriadKNLowRemoteSpectralDatumRound98Exact where

------------------------------------------------------------------------
-- STRICT B-PHASE S2b2c2b / LITERAL LOW-REMOTE R98 SPECTRAL DATUM
--
-- Upstream #957 owners already provide:
--   * exact low/collar/remote packet selectors;
--   * a genuine two-shell integer Euclidean frequency gap;
--   * transport of that gap onto the SAME rational C3.normSquared carrier
--     used by the live viscous term.
--
-- This file lifts those pointwise live-frequency bounds through the literal
-- finite R98 packet sums.  The only physical order premise is 0 <= nu.
-- This is intentionally weaker than, and logically independent from, the
-- later S4 retained-viscosity condition 0 < 2 nu - a.
--
-- R98 uses half-energy
--
--   E_P = (1/2) sum_P |u_k|^2,
--
-- while R407 contributes
--
--   D_P = nu sum_P |k|^2 |u_k|^2.
--
-- Hence the spectral rates in R98's abstract datum are exactly
--
--   lambda_low    = 2 nu omega_low,
--   lambda_remote = 2 nu omega_remote.
--
-- No collar estimate and no final S2b2 inequality is proved here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (_≤?_)
import Data.Nat.Properties as Nat
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3EuclideanSelfPairing as Self
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as Euclidean
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as S0
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as R30
import DASHI.Physics.Closure.NSTriadKNCanonicalLiteralProjectedODERound407Exact as R407
import DASHI.Physics.Closure.NSTriadKNPhysicalPacketBoundaryFluxLogReserveRound98Exact as Packet
import DASHI.Physics.Closure.NSTriadKNOffPacketRatioBoundaryFluxCoerciveRound98Exact as Ratio
import DASHI.Physics.Closure.NSTriadKNOffPacketSpectralCrossDissipationRound98Exact as Spectral
import DASHI.Physics.Closure.NSTriadKNLowCollarRemotePacketSplitExact as Split
import DASHI.Physics.Closure.NSTriadKNRationalIntegerEmbeddingModeNormScaleExact as Scale
import DASHI.Physics.Closure.NSTriadKNDyadicEuclideanShellMarginRound88Exact as R88
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNF4ProjectedOutputPairingRound39Exact as Pairing

F : C3.RealField _
F = Rational.rationalRealField

two : ℚ
two = 1ℚ + 1ℚ

oneNonnegative : 0ℚ ≤ 1ℚ
oneNonnegative = ℚP.nonNegative⁻¹ 1ℚ

twoNonnegative : 0ℚ ≤ two
twoNonnegative = Rational.addNonnegative oneNonnegative oneNonnegative

------------------------------------------------------------------------
-- Literal modal mass and selected-energy positivity.
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
... | false
  rewrite ℚP.+-identityˡ
    (Packet.sumSelectedPairing selected velocity velocity rest) =
  selectedSelfSumNonnegative selected velocity rest
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
-- The live R407 viscous selected pairing is nu |k|^2 times modal mass.
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
... | false
  rewrite ℚP.+-identityˡ
      (Packet.sumSelectedPairing selected
        (Audit.velocity (R30.finiteSystem physical))
        (R407.positiveViscousCoefficient physical) rest)
        | ℚP.+-identityˡ
      (Packet.sumSelectedPairing selected
        (Audit.velocity (R30.finiteSystem physical))
        (Audit.velocity (R30.finiteSystem physical)) rest) =
  selectedDissipationUpper physical selected ceiling nuNN pointwise rest
... | true =
  let
    u = Audit.velocity (R30.finiteSystem physical) mode
    mass = Pairing.realHermitianPower u u
    massNN : 0ℚ ≤ mass
    massNN = subst
      (λ value → 0ℚ ≤ value)
      (sym (selfPowerIsModalMass u))
      (modalMassNonnegative u)
    frequency = C3.normSquared (R30.physicalInverseSquare physical) mode
    frequency≤ = pointwise mode refl
    scaledFrequency≤ :
      R30.viscosity physical * frequency
      ≤ R30.viscosity physical * ceiling
    scaledFrequency≤ =
      let instance nuNonnegative = nonNegative nuNN
      in ℚP.*-monoˡ-≤-nonNeg (R30.viscosity physical) frequency≤
    head≤ :
      (R30.viscosity physical * frequency) * mass
      ≤ (R30.viscosity physical * ceiling) * mass
    head≤ =
      let instance massNonnegative = nonNegative massNN
      in ℚP.*-monoʳ-≤-nonNeg mass scaledFrequency≤
    tail≤ = selectedDissipationUpper
      physical selected ceiling nuNN pointwise rest
    added = ℚP.+-mono-≤ head≤ tail≤
    tailMass = Packet.sumSelectedPairing selected
      (Audit.velocity (R30.finiteSystem physical))
      (Audit.velocity (R30.finiteSystem physical)) rest
    distribute :
      (R30.viscosity physical * ceiling) * (mass + tailMass)
      ≡
      (R30.viscosity physical * ceiling) * mass
        + (R30.viscosity physical * ceiling) * tailMass
    distribute = solve
      (R30.viscosity physical ∷ ceiling ∷ mass ∷ tailMass ∷ [])
  in
  rewrite selectedViscousTermMeaning physical selected mode =
    subst
      (λ right →
        (R30.viscosity physical * frequency) * mass
          + Packet.sumSelectedPairing selected
              (Audit.velocity (R30.finiteSystem physical))
              (R407.positiveViscousCoefficient physical) rest
        ≤ right)
      (sym distribute)
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
... | false
  rewrite ℚP.+-identityˡ
      (Packet.sumSelectedPairing selected
        (Audit.velocity (R30.finiteSystem physical))
        (Audit.velocity (R30.finiteSystem physical)) rest)
        | ℚP.+-identityˡ
      (Packet.sumSelectedPairing selected
        (Audit.velocity (R30.finiteSystem physical))
        (R407.positiveViscousCoefficient physical) rest) =
  selectedDissipationLower physical selected floor nuNN pointwise rest
... | true =
  let
    u = Audit.velocity (R30.finiteSystem physical) mode
    mass = Pairing.realHermitianPower u u
    massNN : 0ℚ ≤ mass
    massNN = subst
      (λ value → 0ℚ ≤ value)
      (sym (selfPowerIsModalMass u))
      (modalMassNonnegative u)
    frequency = C3.normSquared (R30.physicalInverseSquare physical) mode
    floor≤frequency = pointwise mode refl
    scaledFloor≤ :
      R30.viscosity physical * floor
      ≤ R30.viscosity physical * frequency
    scaledFloor≤ =
      let instance nuNonnegative = nonNegative nuNN
      in ℚP.*-monoˡ-≤-nonNeg (R30.viscosity physical) floor≤frequency
    head≤ :
      (R30.viscosity physical * floor) * mass
      ≤ (R30.viscosity physical * frequency) * mass
    head≤ =
      let instance massNonnegative = nonNegative massNN
      in ℚP.*-monoʳ-≤-nonNeg mass scaledFloor≤
    tail≤ = selectedDissipationLower
      physical selected floor nuNN pointwise rest
    added = ℚP.+-mono-≤ head≤ tail≤
    tailMass = Packet.sumSelectedPairing selected
      (Audit.velocity (R30.finiteSystem physical))
      (Audit.velocity (R30.finiteSystem physical)) rest
    distribute :
      (R30.viscosity physical * floor) * (mass + tailMass)
      ≡
      (R30.viscosity physical * floor) * mass
        + (R30.viscosity physical * floor) * tailMass
    distribute = solve
      (R30.viscosity physical ∷ floor ∷ mass ∷ tailMass ∷ [])
  in
  rewrite selectedViscousTermMeaning physical selected mode =
    subst
      (λ left → left ≤
        (R30.viscosity physical * frequency) * mass
          + Packet.sumSelectedPairing selected
              (Audit.velocity (R30.finiteSystem physical))
              (R407.positiveViscousCoefficient physical) rest)
      (sym distribute)
      added

------------------------------------------------------------------------
-- Literal low/remote selector facts.
------------------------------------------------------------------------

lowSelectedImpliesShellBelow :
  (K : Nat) (mode : Z3.FourierMode) →
  Split.lowPacket (suc K) mode ≡ true →
  Shell.shellIndex mode < suc K
lowSelectedImpliesShellBelow K mode selectedTrue
  with Output.modeEqual mode Z3.zeroMode
     | suc K ≤? Shell.shellIndex mode
... | true | decision =
  subst
    (λ chosen → Shell.shellIndex chosen < suc K)
    (sym (Output.modeEqualSound refl))
    (s≤s z≤n)
... | false | yes threshold≤ = Output.falseNotTrue selectedTrue
... | false | no thresholdNot≤ = Nat.≰⇒> thresholdNot≤

remoteSelectedImpliesShellAbove :
  (K : Nat) (mode : Z3.FourierMode) →
  Split.remotePacket (suc K) mode ≡ true →
  suc (suc K) ≤ Shell.shellIndex mode
remoteSelectedImpliesShellAbove K mode selectedTrue
  with Output.modeEqual mode Z3.zeroMode
     | suc (suc K) ≤? Shell.shellIndex mode
... | true | decision = Output.falseNotTrue selectedTrue
... | false | yes threshold≤ = threshold≤
... | false | no thresholdNot≤ = Output.falseNotTrue selectedTrue

------------------------------------------------------------------------
-- Literal packet datum.
------------------------------------------------------------------------

lowFrequency : C3.IntegerEmbedding F → Nat → ℚ
lowFrequency E K =
  Scale.scaledNatFrequency E (3 * R88.natSquare (Shell.pow2 K))

remoteFrequency : C3.IntegerEmbedding F → Nat → ℚ
remoteFrequency E K =
  Scale.scaledNatFrequency E (4 * R88.natSquare (Shell.pow2 K))

spectralRate : ℚ → ℚ → ℚ
spectralRate nu frequency = two * nu * frequency

frequencyNonnegative :
  (E : C3.IntegerEmbedding F) (n : Nat) →
  0ℚ ≤ Scale.scaledNatFrequency E n
frequencyNonnegative E n =
  let
    unitNN = Scale.unitSquareNonnegative E
    natNN = Scale.natAsRationalNonnegative n
    instance
      unitNonnegative = nonNegative unitNN
      natNonnegative = nonNegative natNN
      productNonnegative = ℚP.nonNeg*nonNeg⇒nonNeg
        (Scale.unitSquare E) (S0.natAsRational n)
  in ℚP.nonNegative⁻¹ _

spectralRateNonnegative :
  ∀ nu frequency →
  0ℚ ≤ nu → 0ℚ ≤ frequency →
  0ℚ ≤ spectralRate nu frequency
spectralRateNonnegative nu frequency nuNN frequencyNN =
  let
    twoNuNN : 0ℚ ≤ two * nu
    twoNuNN =
      let instance
        twoNonnegativeInstance = nonNegative twoNonnegative
        nuNonnegativeInstance = nonNegative nuNN
        productNonnegative = ℚP.nonNeg*nonNeg⇒nonNeg two nu
      in ℚP.nonNegative⁻¹ _
  in
  let instance
      twoNuNonnegative = nonNegative twoNuNN
      frequencyNonnegativeInstance = nonNegative frequencyNN
      productNonnegative = ℚP.nonNeg*nonNeg⇒nonNeg (two * nu) frequency
  in ℚP.nonNegative⁻¹ _

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
    normalization :
      spectralRate (R30.viscosity physical) ceiling * (Ratio.oneHalf * mass)
      ≡ (R30.viscosity physical * ceiling) * mass
    normalization = solve
      (R30.viscosity physical ∷ ceiling ∷ mass ∷ [])
  in
  subst
    (λ right →
      Packet.literalPacketDissipation
        (R30.finiteSystem physical)
        (R407.canonicalLiteralProjectedEquation physical) selected ≤ right)
    (sym normalization)
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
    normalization :
      spectralRate (R30.viscosity physical) floor * (Ratio.oneHalf * mass)
      ≡ (R30.viscosity physical * floor) * mass
    normalization = solve
      (R30.viscosity physical ∷ floor ∷ mass ∷ [])
  in
  subst
    (λ left → left ≤
      Packet.literalPacketDissipation
        (R30.finiteSystem physical)
        (R407.canonicalLiteralProjectedEquation physical) selected)
    normalization
    raw

buildLowRemoteSpectralDatum :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (K : Nat) →
  0ℚ ≤ R30.viscosity physical →
  Spectral.SpectralCrossDissipationDatum
buildLowRemoteSpectralDatum physical K nuNN = record
  { packetEnergy = Ratio.literalSelectedEnergy system low
  ; offPacketEnergy = Ratio.literalSelectedEnergy system remote
  ; packetDissipation = Packet.literalPacketDissipation system ode low
  ; offPacketDissipation = Packet.literalPacketDissipation system ode remote
  ; packetFrequencyCeiling = spectralRate nu lowFreq
  ; offPacketFrequencyFloor = spectralRate nu remoteFreq
  ; packetEnergyNonnegative = literalSelectedEnergyNonnegative system low
  ; offPacketEnergyNonnegative = literalSelectedEnergyNonnegative system remote
  ; packetFrequencyCeilingNonnegative =
      spectralRateNonnegative nu lowFreq nuNN
        (frequencyNonnegative E (3 * R88.natSquare (Shell.pow2 K)))
  ; offPacketFrequencyFloorNonnegative =
      spectralRateNonnegative nu remoteFreq nuNN
        (frequencyNonnegative E (4 * R88.natSquare (Shell.pow2 K)))
  ; packetDissipationUpper =
      selectedDissipationUpperAsEnergy physical low lowFreq nuNN
        (λ mode hit →
          Scale.liveLowFrequencyCeiling E I
            (lowSelectedImpliesShellBelow K mode hit))
  ; offPacketDissipationLower =
      selectedDissipationLowerAsEnergy physical remote remoteFreq nuNN
        (λ mode hit →
          Scale.liveRemoteFrequencyFloor E I
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
  spectralRate (R30.viscosity physical)
      (lowFrequency (R30.physicalEmbedding physical) K)
  ≤ spectralRate (R30.viscosity physical)
      (remoteFrequency (R30.physicalEmbedding physical) K)
lowRateBelowRemoteRate physical K nuNN =
  let
    base = Scale.liveLowCeilingBelowRemoteFloor
      (R30.physicalEmbedding physical) K
    twoNuNN : 0ℚ ≤ two * R30.viscosity physical
    twoNuNN =
      let instance
        twoNonnegativeInstance = nonNegative twoNonnegative
        nuNonnegativeInstance = nonNegative nuNN
        productNonnegative = ℚP.nonNeg*nonNeg⇒nonNeg
          two (R30.viscosity physical)
      in ℚP.nonNegative⁻¹ _
    instance scaleNonnegative = nonNegative twoNuNN
  in
  ℚP.*-monoˡ-≤-nonNeg (two * R30.viscosity physical) base

lowRemotePositiveSpectralGap :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (K : Nat) →
  (nuNN : 0ℚ ≤ R30.viscosity physical) →
  Spectral.PositiveSpectralGap
    (buildLowRemoteSpectralDatum physical K nuNN)
lowRemotePositiveSpectralGap physical K nuNN = record
  { gapPositive = gapNN }
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
