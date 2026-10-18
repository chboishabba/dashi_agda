{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNRadialConservationToPhysicalLayerCakeRound647Exact where

------------------------------------------------------------------------
-- ROUND647 / CONSERVATIVE RADIAL TRANSFER -> PHYSICAL UPPER-SHELL LAYER-CAKE
--
-- R646 normalizes the strict-margin C2 surplus on
--
--   radialWeightedTransfer system modes.
--
-- R104 already proves the finite Abel identity
--
--   weightedTransfer = baseWeight * totalTransfer + radialLayerCake.
--
-- Therefore the only algebraic seam before the existing physical packet weld
-- is to transport ordinary nonlinear-energy conservation through the radial
-- sort.  This file closes exactly that seam.
--
-- No quantitative estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Nat.Properties using (_≤?_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Reality
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as R34
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalProductionRadialOrderExact as Radial
import DASHI.Physics.Closure.NSTriadKNLiteralUpperShellCanonicalSuffixExact as Canonical
import DASHI.Physics.Closure.NSTriadKNCriticalProductionPacketLayerCakeRound104Exact as LayerCake
import DASHI.Physics.Closure.NSTriadKNR104GlobalLayerCakePhysicalPacketWeldExact as Physical

F : C3.RealField _
F = Rational.rationalRealField

rawModeTerm :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → ℚ
rawModeTerm system mode =
  Canonical.rawProjectedPairing system (mode ∷ [])

rawInsertPreservesPairing :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (mode : Z3.FourierMode) →
  (modes : List Z3.FourierMode) →
  Canonical.rawProjectedPairing system (Radial.insertByShell mode modes)
  ≡ rawModeTerm system mode + Canonical.rawProjectedPairing system modes
rawInsertPreservesPairing system mode [] = refl
rawInsertPreservesPairing system mode (head ∷ rest)
  with Shell.shellIndex mode ≤? Shell.shellIndex head
... | yes mode≤head = refl
... | no mode≰head
  rewrite rawInsertPreservesPairing system mode rest =
  solve
    ( rawModeTerm system mode
    ∷ rawModeTerm system head
    ∷ Canonical.rawProjectedPairing system rest
    ∷ [] )

rawSortPreservesPairing :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (modes : List Z3.FourierMode) →
  Canonical.rawProjectedPairing system (Radial.sortByShell modes)
  ≡ Canonical.rawProjectedPairing system modes
rawSortPreservesPairing system [] = refl
rawSortPreservesPairing system (mode ∷ rest) =
  trans
    (rawInsertPreservesPairing system mode (Radial.sortByShell rest))
    (cong (rawModeTerm system mode +_)
      (rawSortPreservesPairing system rest))

radialTotalTransferZero :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (modes : List Z3.FourierMode) →
  Canonical.rawProjectedPairing system modes ≡ 0ℚ →
  LayerCake.totalTransfer (Radial.radialBandTransfers system modes) ≡ 0ℚ
radialTotalTransferZero system modes conservation =
  trans
    (Canonical.literalBandTotalTransferIsRawPairing
      system (Radial.sortByShell modes))
    (trans
      (rawSortPreservesPairing system modes)
      conservation)

radialWeightedTransferIsLayerCake :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (modes : List Z3.FourierMode) →
  Canonical.rawProjectedPairing system modes ≡ 0ℚ →
  LayerCake.weightedTransfer (Radial.radialBandTransfers system modes)
  ≡ LayerCake.radialLayerCake (Radial.radialBandTransfers system modes)
radialWeightedTransferIsLayerCake system modes conservation =
  LayerCake.conservativeWeightedTransferIsLayerCake
    (Radial.radialBandTransfers system modes)
    (radialTotalTransferZero system modes conservation)

canonicalRadialWeightedTransferIsPhysicalUpperShellLayerCake :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  Reality.RealityCondition (Audit.velocity system) →
  Reality.DivergenceFreeCondition E (Audit.velocity system) →
  Canonical.rawProjectedPairing system
    (R34.nonzeroCutoffModes (Audit.cutoff system)) ≡ 0ℚ →
  LayerCake.weightedTransfer
      (Radial.radialBandTransfers system
        (R34.nonzeroCutoffModes (Audit.cutoff system)))
  ≡ Physical.physicalUpperShellLayerCake system
      (Physical.canonicalSortedModes system)
canonicalRadialWeightedTransferIsPhysicalUpperShellLayerCake
    system reality divergenceFree conservation =
  trans
    (radialWeightedTransferIsLayerCake
      system
      (R34.nonzeroCutoffModes (Audit.cutoff system))
      conservation)
    (Physical.canonicalR104LayerCakeIsPhysicalUpperShellLayerCake
      system reality divergenceFree)

round647RawPairingSortInvariantClosed : Bool
round647RawPairingSortInvariantClosed = true

round647ConservationToRadialLayerCakeClosed : Bool
round647ConservationToRadialLayerCakeClosed = true

round647CanonicalRadialTransferToPhysicalPacketLayerCakeClosed : Bool
round647CanonicalRadialTransferToPhysicalPacketLayerCakeClosed = true

round647IntroducesQuantitativeEstimate : Bool
round647IntroducesQuantitativeEstimate = false

round647ClayPromotion : Bool
round647ClayPromotion = false

round647RawPairingSortInvariantClosedIsTrue :
  round647RawPairingSortInvariantClosed ≡ true
round647RawPairingSortInvariantClosedIsTrue = refl

round647ConservationToRadialLayerCakeClosedIsTrue :
  round647ConservationToRadialLayerCakeClosed ≡ true
round647ConservationToRadialLayerCakeClosedIsTrue = refl

round647CanonicalRadialTransferToPhysicalPacketLayerCakeClosedIsTrue :
  round647CanonicalRadialTransferToPhysicalPacketLayerCakeClosed ≡ true
round647CanonicalRadialTransferToPhysicalPacketLayerCakeClosedIsTrue = refl

round647IntroducesQuantitativeEstimateIsFalse :
  round647IntroducesQuantitativeEstimate ≡ false
round647IntroducesQuantitativeEstimateIsFalse = refl

round647ClayPromotionIsFalse :
  round647ClayPromotion ≡ false
round647ClayPromotionIsFalse = refl
