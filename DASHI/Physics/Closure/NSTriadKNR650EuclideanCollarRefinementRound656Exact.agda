{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650EuclideanCollarRefinementRound656Exact where

------------------------------------------------------------------------
-- ROUND656 / EUCLIDEAN-RADIUS REFINEMENT OF THE R655 COLLAR
--
-- R655 proves that the full low-complement R98 spectral cross is bounded by
-- the exact-shell collar cross.  The adjacent-shell no-go shows why the WHOLE
-- max-norm collar cannot be assigned a favorable Euclidean spectral sign.
--
-- But only part of the collar is problematic.
--
-- For threshold j = suc K, every low mode obeys the live ceiling
--
--     |k_low|^2 <= c^2 * 3 * (2^K)^2.
--
-- Split the exact shell-j collar by its literal integer Euclidean radius:
--
--   good collar:
--     modeNatNormSquared >= 3 * (2^K)^2;
--
--   bad collar:
--     modeNatNormSquared <  3 * (2^K)^2.
--
-- The good collar therefore has the SAME live frequency floor as the low
-- packet ceiling.  R98 spectral-cross coercivity applies with zero/nonnegative
-- gap and makes the good-collar cross nonpositive.
--
-- Hence
--
--   full low-complement cross <= bad-collar cross.
--
-- This removes both the remote cross and the spectrally good collar cross from
-- the adverse ratio dynamics.  The surviving hard geometry is only the
-- low-radius cap of one exact max-norm shell.
--
-- No boundary-flux payment, signed collar-flux estimate, or Clay promotion is
-- introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Nat.Properties using (_≤?_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSPeriodicConcreteIntegerModeNorm as ModeNorm
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNF4ProjectedOutputPairingRound39Exact as Pairing
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as R30
import DASHI.Physics.Closure.NSTriadKNCanonicalLiteralProjectedODERound407Exact as R407
import DASHI.Physics.Closure.NSTriadKNPhysicalPacketBoundaryFluxLogReserveRound98Exact as Packet
import DASHI.Physics.Closure.NSTriadKNOffPacketRatioBoundaryFluxCoerciveRound98Exact as Ratio
import DASHI.Physics.Closure.NSTriadKNLowCollarRemotePacketSplitExact as Split
import DASHI.Physics.Closure.NSTriadKNLowRemoteSpectralDatumRound98Exact as Remote
import DASHI.Physics.Closure.NSTriadKNOffPacketSpectralCrossDissipationRound98Exact as Spectral
import DASHI.Physics.Closure.NSTriadKNRationalIntegerEmbeddingModeNormScaleExact as Scale
import DASHI.Physics.Closure.NSTriadKNDyadicEuclideanShellMarginRound88Exact as R88
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNR650LowCollarRemoteCrossReductionRound655Exact as R655

F : C3.RealField _
F = Rational.rationalRealField

lowCeilingNat : Nat → Nat
lowCeilingNat K = 3 * R88.natSquare (Shell.pow2 K)

goodCollarPacket : Nat → Z3.FourierMode → Bool
goodCollarPacket K mode
  with Split.collarPacket (suc K) mode
     | lowCeilingNat K ≤? ModeNorm.modeNatNormSquared mode
... | true | yes _ = true
... | _ | _ = false

badCollarPacket : Nat → Z3.FourierMode → Bool
badCollarPacket K mode
  with Split.collarPacket (suc K) mode
     | lowCeilingNat K ≤? ModeNorm.modeNatNormSquared mode
... | true | no _ = true
... | _ | _ = false

------------------------------------------------------------------------
-- Exact collar = bad + good selector partition.
------------------------------------------------------------------------

selectedPairingCollarRefinement :
  (K : Nat) →
  (test value : Z3.FourierMode → C3.Complex3 F) →
  (mode : Z3.FourierMode) →
  Packet.selectedPairing (Split.collarPacket (suc K)) test value mode
  ≡
  Packet.selectedPairing (badCollarPacket K) test value mode
    + Packet.selectedPairing (goodCollarPacket K) test value mode
selectedPairingCollarRefinement K test value mode
  with Split.collarPacket (suc K) mode
     | lowCeilingNat K ≤? ModeNorm.modeNatNormSquared mode
... | false | yes _ = refl
... | false | no _ = refl
... | true | yes _ =
  solve (Pairing.realHermitianPower (test mode) (value mode) ∷ [])
... | true | no _ =
  solve (Pairing.realHermitianPower (test mode) (value mode) ∷ [])

sumSelectedPairingCollarRefinement :
  (K : Nat) →
  (test value : Z3.FourierMode → C3.Complex3 F) →
  (modes : List Z3.FourierMode) →
  Packet.sumSelectedPairing (Split.collarPacket (suc K)) test value modes
  ≡
  Packet.sumSelectedPairing (badCollarPacket K) test value modes
    + Packet.sumSelectedPairing (goodCollarPacket K) test value modes
sumSelectedPairingCollarRefinement K test value [] = refl
sumSelectedPairingCollarRefinement K test value (mode ∷ rest)
  rewrite selectedPairingCollarRefinement K test value mode
        | sumSelectedPairingCollarRefinement K test value rest =
  solve
    ( Packet.selectedPairing (badCollarPacket K) test value mode
    ∷ Packet.selectedPairing (goodCollarPacket K) test value mode
    ∷ Packet.sumSelectedPairing (badCollarPacket K) test value rest
    ∷ Packet.sumSelectedPairing (goodCollarPacket K) test value rest
    ∷ [])

literalEnergyCollarRefinement :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (K : Nat) →
  let system = R30.finiteSystem physical
  in
  Ratio.literalSelectedEnergy system (Split.collarPacket (suc K))
  ≡
  Ratio.literalSelectedEnergy system (badCollarPacket K)
    + Ratio.literalSelectedEnergy system (goodCollarPacket K)
literalEnergyCollarRefinement physical K =
  let
    system = R30.finiteSystem physical
    velocity = Audit.velocity system
    modes = Cube.cutoffModes (Audit.cutoff system)
    raw = sumSelectedPairingCollarRefinement K velocity velocity modes
  in
  trans
    (cong (Ratio.oneHalf *_) raw)
    (solve
      ( Ratio.oneHalf
      ∷ Packet.sumSelectedPairing (badCollarPacket K) velocity velocity modes
      ∷ Packet.sumSelectedPairing (goodCollarPacket K) velocity velocity modes
      ∷ []))

literalDissipationCollarRefinement :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (K : Nat) →
  R655.literalPacketDissipation physical (Split.collarPacket (suc K))
  ≡
  R655.literalPacketDissipation physical (badCollarPacket K)
    + R655.literalPacketDissipation physical (goodCollarPacket K)
literalDissipationCollarRefinement physical K =
  let
    system = R30.finiteSystem physical
    ode = R407.canonicalLiteralProjectedEquation physical
    velocity = Audit.velocity system
    viscous = Audit.viscousTerm ode
    modes = Cube.cutoffModes (Audit.cutoff system)
  in
  sumSelectedPairingCollarRefinement K velocity viscous modes

------------------------------------------------------------------------
-- Good collar has the low-ceiling Euclidean floor on the SAME live norm.
------------------------------------------------------------------------

goodCollarSelectedImpliesNatFloor :
  (K : Nat) →
  (mode : Z3.FourierMode) →
  goodCollarPacket K mode ≡ true →
  lowCeilingNat K ≤ ModeNorm.modeNatNormSquared mode
goodCollarSelectedImpliesNatFloor K mode hit
  with Split.collarPacket (suc K) mode
     | lowCeilingNat K ≤? ModeNorm.modeNatNormSquared mode
... | true | yes floor≤ = floor≤
... | true | no _ = Output.falseNotTrue hit
... | false | yes _ = Output.falseNotTrue hit
... | false | no _ = Output.falseNotTrue hit

goodCollarLiveFrequencyFloor :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (K : Nat) →
  (mode : Z3.FourierMode) →
  goodCollarPacket K mode ≡ true →
  Remote.lowFrequency E K ≤ C3.normSquared I mode
goodCollarLiveFrequencyFloor E I K mode hit =
  subst
    (λ right → Remote.lowFrequency E K ≤ right)
    (sym (Scale.modeNormCommonSquareScale E I mode))
    (Scale.scaleMonotone E
      (Scale.natAsRationalMonotone
        (goodCollarSelectedImpliesNatFloor K mode hit)))

------------------------------------------------------------------------
-- Literal low/good-collar spectral datum and nonpositive cross.
------------------------------------------------------------------------

buildLowGoodCollarSpectralDatum :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (K : Nat) →
  0ℚ ≤ R30.viscosity physical →
  Spectral.SpectralCrossDissipationDatum
buildLowGoodCollarSpectralDatum physical K nuNN = record
  { packetEnergy = Ratio.literalSelectedEnergy system low
  ; offPacketEnergy = Ratio.literalSelectedEnergy system good
  ; packetDissipation = R655.literalPacketDissipation physical low
  ; offPacketDissipation = R655.literalPacketDissipation physical good
  ; packetFrequencyCeiling = rate
  ; offPacketFrequencyFloor = rate
  ; packetEnergyNonnegative = Remote.literalSelectedEnergyNonnegative system low
  ; offPacketEnergyNonnegative = Remote.literalSelectedEnergyNonnegative system good
  ; packetFrequencyCeilingNonnegative =
      Remote.spectralRateNonnegative nu frequency nuNN
        (Remote.frequencyNonnegative E (lowCeilingNat K))
  ; offPacketFrequencyFloorNonnegative =
      Remote.spectralRateNonnegative nu frequency nuNN
        (Remote.frequencyNonnegative E (lowCeilingNat K))
  ; packetDissipationUpper =
      Remote.selectedDissipationUpperAsEnergy physical low frequency nuNN
        (λ mode hit →
          Scale.liveLowFrequencyCeiling E I
            (Remote.lowSelectedImpliesShellBelow K mode hit))
  ; offPacketDissipationLower =
      Remote.selectedDissipationLowerAsEnergy physical good frequency nuNN
        (goodCollarLiveFrequencyFloor E I K)
  }
  where
  system = R30.finiteSystem physical
  E = R30.physicalEmbedding physical
  I = R30.physicalInverseSquare physical
  nu = R30.viscosity physical
  low = Split.lowPacket (suc K)
  good = goodCollarPacket K
  frequency = Remote.lowFrequency E K
  rate = Remote.spectralRate nu frequency

lowGoodCollarNonnegativeGap :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (K : Nat) →
  (nuNN : 0ℚ ≤ R30.viscosity physical) →
  Spectral.PositiveSpectralGap
    (buildLowGoodCollarSpectralDatum physical K nuNN)
lowGoodCollarNonnegativeGap physical K nuNN = record
  { Spectral.gapPositive = gap }
  where
  D = buildLowGoodCollarSpectralDatum physical K nuNN
  rate = Spectral.packetFrequencyCeiling D
  gap : 0ℚ ≤ Spectral.offPacketFrequencyFloor D - rate
  gap =
    subst
      (λ value → 0ℚ ≤ value)
      (sym (solve (rate ∷ [])))
      ℚP.≤-refl

goodCollarCross :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  Nat → ℚ
goodCollarCross physical K =
  let
    system = R30.finiteSystem physical
    low = Split.lowPacket (suc K)
  in
  R655.spectralCross
    (Ratio.literalSelectedEnergy system (goodCollarPacket K))
    (R655.literalPacketDissipation physical low)
    (R655.literalPacketDissipation physical (goodCollarPacket K))
    (Ratio.literalSelectedEnergy system low)

badCollarCross :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  Nat → ℚ
badCollarCross physical K =
  let
    system = R30.finiteSystem physical
    low = Split.lowPacket (suc K)
  in
  R655.spectralCross
    (Ratio.literalSelectedEnergy system (badCollarPacket K))
    (R655.literalPacketDissipation physical low)
    (R655.literalPacketDissipation physical (badCollarPacket K))
    (Ratio.literalSelectedEnergy system low)

goodCollarCrossNonpositive :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (K : Nat) →
  (nuNN : 0ℚ ≤ R30.viscosity physical) →
  goodCollarCross physical K ≤ 0ℚ
goodCollarCrossNonpositive physical K nuNN =
  Spectral.spectralCrossDissipationNonpositive
    (buildLowGoodCollarSpectralDatum physical K nuNN)
    (lowGoodCollarNonnegativeGap physical K nuNN)

collarCrossIsBadPlusGood :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (K : Nat) →
  R655.collarCross physical (suc K)
  ≡ badCollarCross physical K + goodCollarCross physical K
collarCrossIsBadPlusGood physical K =
  let
    system = R30.finiteSystem physical
    low = Split.lowPacket (suc K)
    lowE = Ratio.literalSelectedEnergy system low
    lowD = R655.literalPacketDissipation physical low
    badE = Ratio.literalSelectedEnergy system (badCollarPacket K)
    goodE = Ratio.literalSelectedEnergy system (goodCollarPacket K)
    badD = R655.literalPacketDissipation physical (badCollarPacket K)
    goodD = R655.literalPacketDissipation physical (goodCollarPacket K)
  in
  rewrite literalEnergyCollarRefinement physical K
        | literalDissipationCollarRefinement physical K =
    solve (lowE ∷ lowD ∷ badE ∷ goodE ∷ badD ∷ goodD ∷ [])

fullCrossBelowBadCollar :
  (physical : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (K : Nat) →
  (nuNN : 0ℚ ≤ R30.viscosity physical) →
  R655.fullLowComplementCross physical (suc K)
  ≤ badCollarCross physical K
fullCrossBelowBadCollar physical K nuNN =
  let
    full≤collar = R655.fullCrossBelowCollarCross physical K nuNN
    collarEq = collarCrossIsBadPlusGood physical K
    good≤0 = goodCollarCrossNonpositive physical K nuNN
    bad = badCollarCross physical K
    good = goodCollarCross physical K
    collar≤bad :
      R655.collarCross physical (suc K) ≤ bad
    collar≤bad =
      subst
        (λ left → left ≤ bad)
        (sym collarEq)
        (subst
          (λ right → bad + good ≤ right)
          (solve (bad ∷ []))
          (ℚP.+-mono-≤ ℚP.≤-refl good≤0))
  in
  ℚP.≤-trans full≤collar collar≤bad

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round656ExactCollarEuclideanRefinementClosed : Bool
round656ExactCollarEuclideanRefinementClosed = true

round656GoodCollarSpectralDatumConstructed : Bool
round656GoodCollarSpectralDatumConstructed = true

round656GoodCollarCrossNonpositive : Bool
round656GoodCollarCrossNonpositive = true

round656FullCrossReducedToBadLowRadiusCollar : Bool
round656FullCrossReducedToBadLowRadiusCollar = true

round656BadCollarPaymentClosed : Bool
round656BadCollarPaymentClosed = false

round656BoundaryFluxPaymentClosed : Bool
round656BoundaryFluxPaymentClosed = false

round656IntroducesNewClayLeaf : Bool
round656IntroducesNewClayLeaf = false

round656C2Closed : Bool
round656C2Closed = false

round656ClayPromotion : Bool
round656ClayPromotion = false

round656ExactCollarEuclideanRefinementClosedIsTrue :
  round656ExactCollarEuclideanRefinementClosed ≡ true
round656ExactCollarEuclideanRefinementClosedIsTrue = refl

round656GoodCollarSpectralDatumConstructedIsTrue :
  round656GoodCollarSpectralDatumConstructed ≡ true
round656GoodCollarSpectralDatumConstructedIsTrue = refl

round656GoodCollarCrossNonpositiveIsTrue :
  round656GoodCollarCrossNonpositive ≡ true
round656GoodCollarCrossNonpositiveIsTrue = refl

round656FullCrossReducedToBadLowRadiusCollarIsTrue :
  round656FullCrossReducedToBadLowRadiusCollar ≡ true
round656FullCrossReducedToBadLowRadiusCollarIsTrue = refl

round656BadCollarPaymentClosedIsFalse :
  round656BadCollarPaymentClosed ≡ false
round656BadCollarPaymentClosedIsFalse = refl

round656BoundaryFluxPaymentClosedIsFalse :
  round656BoundaryFluxPaymentClosed ≡ false
round656BoundaryFluxPaymentClosedIsFalse = refl

round656IntroducesNewClayLeafIsFalse :
  round656IntroducesNewClayLeaf ≡ false
round656IntroducesNewClayLeafIsFalse = refl

round656C2ClosedIsFalse :
  round656C2Closed ≡ false
round656C2ClosedIsFalse = refl

round656ClayPromotionIsFalse :
  round656ClayPromotion ≡ false
round656ClayPromotionIsFalse = refl
