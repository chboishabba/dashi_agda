module DASHI.Physics.Closure.NSTriadKNLiteralCriticalProductionBandTransferExact where

------------------------------------------------------------------------
-- STRICT B-PHASE S2b0 / LITERAL CRITICAL PRODUCTION -> R104 BAND CARRIER
--
-- S2a identifies the literal S0 production with twice the dyadic-weighted
-- R39 projected-pairing fold. R104's Abel layer-cake is stated on a finite list
-- of `(weight , transfer)` pairs. This owner closes only that representation
-- seam on the SAME finite mode list:
--
--   mode k |-> ( w(k) , Re <u_k, N_k(u)> ).
--
-- The R104 `weightedTransfer` of this mapped list is exactly S2a's weighted
-- projected-pairing fold, hence S0's instantaneous critical production is
-- exactly twice that R104 weighted transfer.
--
-- IMPORTANT: the incoming mode list is NOT claimed to be radially ordered.
-- Therefore this file does not yet identify R104 suffixes with physical upper
-- packets and does not invoke the conservative Abel reduction. Those are the
-- next same-object/finite-geometry seams. No quantitative S2 estimate is
-- introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as S0
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalProductionProjectedPairingExact as S2a
import DASHI.Physics.Closure.NSTriadKNCriticalProductionPacketLayerCakeRound104Exact as LayerCake

F : C3.RealField _
F = Rational.rationalRealField

literalBandTransfer :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode →
  LayerCake.BandTransfer
literalBandTransfer system mode =
  ( S0.dyadicCriticalWeight mode
  , S2a.weightedProjectedPairing system (mode ∷ [])
  )

-- For one mode, S2a's singleton fold is exactly the unweighted projected
-- pairing, so the R104 band transfer can be exposed without inventing a second
-- scalar observable.
singletonTransferMeaning :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (mode : Z3.FourierMode) →
  LayerCake.transfer (literalBandTransfer system mode)
  ≡ S2a.weightedProjectedPairing system (mode ∷ [])
singletonTransferMeaning system mode = refl

literalBandTransfers :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  List Z3.FourierMode →
  List LayerCake.BandTransfer
literalBandTransfers system [] = []
literalBandTransfers system (mode ∷ rest) =
  literalBandTransfer system mode ∷ literalBandTransfers system rest

------------------------------------------------------------------------
-- Exact weighted fold identity.
--
-- `literalBandTransfer` deliberately stores the singleton S2a fold as the
-- transfer coordinate. Since the singleton S2a fold is itself
--   w(k) * Re<u_k,N_k>,
-- R104's weightedTransfer would square the weight. That is not the desired
-- carrier. Therefore expose the correct raw transfer directly below instead.
------------------------------------------------------------------------

rawLiteralBandTransfer :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode →
  LayerCake.BandTransfer
rawLiteralBandTransfer system mode =
  ( S0.dyadicCriticalWeight mode
  , S2a.R39.realHermitianPower
      (Audit.velocity system mode)
      (Audit.projectedNonlinearity system mode)
  )

rawLiteralBandTransfers :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  List Z3.FourierMode →
  List LayerCake.BandTransfer
rawLiteralBandTransfers system [] = []
rawLiteralBandTransfers system (mode ∷ rest) =
  rawLiteralBandTransfer system mode ∷ rawLiteralBandTransfers system rest

weightedTransferIsWeightedProjectedPairing :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (modes : List Z3.FourierMode) →
  LayerCake.weightedTransfer (rawLiteralBandTransfers system modes)
  ≡ S2a.weightedProjectedPairing system modes
weightedTransferIsWeightedProjectedPairing system [] = refl
weightedTransferIsWeightedProjectedPairing system (mode ∷ rest) =
  cong₂ _+_ refl
    (weightedTransferIsWeightedProjectedPairing system rest)

literalCriticalProductionIsTwiceR104WeightedTransfer :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  S0.criticalProductionRate system
  ≡ S0.two * LayerCake.weightedTransfer
      (rawLiteralBandTransfers system (Audit.modes system))
literalCriticalProductionIsTwiceR104WeightedTransfer system =
  trans
    (S2a.literalCriticalProductionIsTwiceWeightedProjectedPairing system)
    (cong (S0.two *_)
      (sym (weightedTransferIsWeightedProjectedPairing
        system (Audit.modes system))))
  where
  open import Relation.Binary.PropositionalEquality using (sym)

------------------------------------------------------------------------
-- Status / boundary.
------------------------------------------------------------------------

literalCriticalProductionBandTransferEmbeddingClosed : Bool
literalCriticalProductionBandTransferEmbeddingClosed = true

weightedTransferMatchesLiteralProductionCarrierClosed : Bool
weightedTransferMatchesLiteralProductionCarrierClosed = true

literalRadialSuffixRealizationClosed : Bool
literalRadialSuffixRealizationClosed = false

s2QuantitativePacketFluxEstimateClosed : Bool
s2QuantitativePacketFluxEstimateClosed = false

literalCriticalProductionBandTransferEmbeddingClosedIsTrue :
  literalCriticalProductionBandTransferEmbeddingClosed ≡ true
literalCriticalProductionBandTransferEmbeddingClosedIsTrue = refl

weightedTransferMatchesLiteralProductionCarrierClosedIsTrue :
  weightedTransferMatchesLiteralProductionCarrierClosed ≡ true
weightedTransferMatchesLiteralProductionCarrierClosedIsTrue = refl

literalRadialSuffixRealizationClosedIsFalse :
  literalRadialSuffixRealizationClosed ≡ false
literalRadialSuffixRealizationClosedIsFalse = refl

s2QuantitativePacketFluxEstimateClosedIsFalse :
  s2QuantitativePacketFluxEstimateClosed ≡ false
s2QuantitativePacketFluxEstimateClosedIsFalse = refl
