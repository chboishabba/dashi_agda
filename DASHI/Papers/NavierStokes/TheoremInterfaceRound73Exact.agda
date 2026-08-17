module DASHI.Papers.NavierStokes.TheoremInterfaceRound73Exact where

------------------------------------------------------------------------
-- PAPER-FACING ROUND73 DELTA
--
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Ole Christensen.
-- Title: "An Introduction to Frames and Riesz Bases".
-- DOI: 10.1007/978-3-319-25613-9.
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Jean-Pierre Serre.
-- Title: "Linear Representations of Finite Groups".
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- Author: Terence Tao.
-- Title: "Quantitative bounds for critically bounded solutions to the
-- Navier-Stokes equations".
-- DOI: 10.1090/PSPUM/104/01874.
--
-- Authors: Tobias Barker; Christophe Prange.
-- Title: "Quantitative Regularity for the Navier-Stokes Equations Via
-- Spatial Concentration".
-- DOI: 10.1007/s00220-021-04122-x.
--
-- ROUND73 PAPER DELTA
--
-- Round72 killed raw polynomial lattice cardinality as a sufficient funding
-- invariant.  Round73 now has one same-object concentration/funding spine:
--
--   source-native factorization a_tau=x_tau y_tau
--   -> mu^2 <= Q W
--   -> favorable physical normalization W<=1 gives mu^2<=Q
--   -> Q is identified with actual event charge
--   -> Carleson node has floor exactly mu^2 and charge exactly Q
--   -> additive physical descendants share one finite budget.
--
-- General frame control W<=B E_phys is also retained when W<=1 is too strong.
-- Exact C2 exchange-odd sectors cancel before majorization, but physical HH/CC
-- exchange identification remains fail-closed.
--
-- The decisive physical theorem is no longer an atom-cardinality bound.  It is
-- the construction of the literal velocity/projector factor source together
-- with a physical frame/normalization and charge identity on the same localized
-- trajectory, followed by additive descendant propagation whose cumulative
-- squared-amplification floors exceed the finite budget.
--
-- Clay promotion remains false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Papers.NavierStokes.TheoremInterfaceRound72Exact
import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound73Exact as R73

round73PaperFrameComplexityAlgebra : Bool
round73PaperFrameComplexityAlgebra = R73.round73FrameComplexityAlgebraConstructed

round73PaperFactorizationAuthorityCarrier : Bool
round73PaperFactorizationAuthorityCarrier =
  R73.round73FactorizationAuthorityCarrierConstructed

round73PaperLowLegFactorizationCarrier : Bool
round73PaperLowLegFactorizationCarrier = R73.round73LowLegFactorizationCarrierConstructed

round73PaperExchangeCancellation : Bool
round73PaperExchangeCancellation = R73.round73ExchangeCancellationConstructed

round73PaperNormalizedComplexityRemovesCardinalityLoss : Bool
round73PaperNormalizedComplexityRemovesCardinalityLoss =
  R73.round73NormalizedComplexityRemovesCardinalityLoss

round73PaperSquareFundingCompiler : Bool
round73PaperSquareFundingCompiler = R73.round73SquareFundingCompilerConstructed

round73PaperNormalizedOverlayPhysicalChargeBridge : Bool
round73PaperNormalizedOverlayPhysicalChargeBridge =
  R73.round73NormalizedOverlayPhysicalChargeBridgeConstructed

round73PaperSquareFundingCarlesonUnified : Bool
round73PaperSquareFundingCarlesonUnified = R73.round73SquareFundingCarlesonUnified

round73PaperPhysicalNormalizedWitnessDirectCarleson : Bool
round73PaperPhysicalNormalizedWitnessDirectCarleson =
  R73.round73PhysicalNormalizedWitnessCompilesDirectlyToCarlesonNode

round73PaperHalfAmplitudeNeedsFourWayChargeMultiplicity : Bool
round73PaperHalfAmplitudeNeedsFourWayChargeMultiplicity =
  R73.round73HalfAmplitudeNeedsFourWayChargeMultiplicity

round73PaperLiteralVelocityProjectorFactorization : Bool
round73PaperLiteralVelocityProjectorFactorization =
  R73.round73LiteralVelocityProjectorProducesSourceNativeTriadicFactorization

round73PaperPhysicalTriadicFrameNormalizationAndChargeIdentity : Bool
round73PaperPhysicalTriadicFrameNormalizationAndChargeIdentity =
  R73.round73PhysicalTriadicFrameNormalizationAndChargeIdentity

round73PaperAdditiveNormalizedDescendants : Bool
round73PaperAdditiveNormalizedDescendants =
  R73.round73PhysicalPropagationProducesAdditiveNormalizedDescendants

round73PaperCumulativeSquaredFloorsOutrunBudget : Bool
round73PaperCumulativeSquaredFloorsOutrunBudget =
  R73.round73CumulativeSquaredAmplificationFloorsOutrunBudget

round73PaperClayPromotion : Bool
round73PaperClayPromotion = R73.round73ClayPromotion

round73PaperNormalizedComplexityRemovesCardinalityLossIsTrue :
  round73PaperNormalizedComplexityRemovesCardinalityLoss ≡ true
round73PaperNormalizedComplexityRemovesCardinalityLossIsTrue = refl

round73PaperSquareFundingCarlesonUnifiedIsTrue :
  round73PaperSquareFundingCarlesonUnified ≡ true
round73PaperSquareFundingCarlesonUnifiedIsTrue = refl

round73PaperPhysicalNormalizedWitnessDirectCarlesonIsTrue :
  round73PaperPhysicalNormalizedWitnessDirectCarleson ≡ true
round73PaperPhysicalNormalizedWitnessDirectCarlesonIsTrue = refl

round73PaperLiteralVelocityProjectorFactorizationIsFalse :
  round73PaperLiteralVelocityProjectorFactorization ≡ false
round73PaperLiteralVelocityProjectorFactorizationIsFalse = refl

round73PaperAdditiveNormalizedDescendantsIsFalse :
  round73PaperAdditiveNormalizedDescendants ≡ false
round73PaperAdditiveNormalizedDescendantsIsFalse = refl

round73PaperClayPromotionIsFalse : round73PaperClayPromotion ≡ false
round73PaperClayPromotionIsFalse = refl
