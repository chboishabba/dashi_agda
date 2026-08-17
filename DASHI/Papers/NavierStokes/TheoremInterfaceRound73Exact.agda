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
-- Round73 now has one same-object concentration/funding spine and a literal
-- Fourier source factorization:
--
--   -i P_k[(u_p dot q)u_q]
--     = [-i(u_p dot q)] P_k u_q,
--
--   <test_k,term>
--     = [-i(u_p dot q)] <test_k,P_k u_q>.
--
-- A cancelling phase witness z=x theta, w=y conjugate(theta), |theta|^2=1
-- compiles this concrete complex product to the real amplitude product x*y.
-- Thus the remaining LH/HL scalar producer is specifically the physical phase
-- alignment theorem on the literal velocity/projector data, not an arbitrary
-- post-hoc rational factorization.
--
-- Frame control, normalized square-charge funding and the Carleson ledger are
-- already composed downstream. Clay promotion remains false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Papers.NavierStokes.TheoremInterfaceRound72Exact
import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound73Exact as R73

round73PaperFrameComplexityAlgebra : Bool
round73PaperFrameComplexityAlgebra = R73.round73FrameComplexityAlgebraConstructed

round73PaperFactorizationAuthorityCarrier : Bool
round73PaperFactorizationAuthorityCarrier = R73.round73FactorizationAuthorityCarrierConstructed

round73PaperLowLegFactorizationCarrier : Bool
round73PaperLowLegFactorizationCarrier = R73.round73LowLegFactorizationCarrierConstructed

round73PaperExchangeCancellation : Bool
round73PaperExchangeCancellation = R73.round73ExchangeCancellationConstructed

round73PaperFrameProductCompilesToNormalizedComplexity : Bool
round73PaperFrameProductCompilesToNormalizedComplexity =
  R73.round73FrameProductCompilesToNormalizedComplexity

round73PaperSquareFundingCarlesonUnified : Bool
round73PaperSquareFundingCarlesonUnified = R73.round73SquareFundingCarlesonUnified

round73PaperLerayComplexScalarLinearity : Bool
round73PaperLerayComplexScalarLinearity = R73.round73LerayComplexScalarLinearityConstructed

round73PaperLiteralComplexOrderedFactorization : Bool
round73PaperLiteralComplexOrderedFactorization = R73.round73LiteralComplexOrderedFactorizationConstructed

round73PaperTestedComplexProductFactorization : Bool
round73PaperTestedComplexProductFactorization = R73.round73TestedComplexProductFactorizationConstructed

round73PaperPhaseCancellationCompiler : Bool
round73PaperPhaseCancellationCompiler = R73.round73PhaseCancellationCompilerConstructed

round73PaperPhaseAlignmentCompilesLiteralSignedCoefficient : Bool
round73PaperPhaseAlignmentCompilesLiteralSignedCoefficient =
  R73.round73PhaseAlignmentCompilesLiteralSignedCoefficient

round73PaperPhysicalOrderedInteractionPhaseAlignment : Bool
round73PaperPhysicalOrderedInteractionPhaseAlignment =
  R73.round73PhysicalOrderedInteractionPhaseAlignment

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

round73PaperLiteralComplexOrderedFactorizationIsTrue :
  round73PaperLiteralComplexOrderedFactorization ≡ true
round73PaperLiteralComplexOrderedFactorizationIsTrue = refl

round73PaperPhaseCancellationCompilerIsTrue :
  round73PaperPhaseCancellationCompiler ≡ true
round73PaperPhaseCancellationCompilerIsTrue = refl

round73PaperPhaseAlignmentCompilesLiteralSignedCoefficientIsTrue :
  round73PaperPhaseAlignmentCompilesLiteralSignedCoefficient ≡ true
round73PaperPhaseAlignmentCompilesLiteralSignedCoefficientIsTrue = refl

round73PaperPhysicalOrderedInteractionPhaseAlignmentIsFalse :
  round73PaperPhysicalOrderedInteractionPhaseAlignment ≡ false
round73PaperPhysicalOrderedInteractionPhaseAlignmentIsFalse = refl

round73PaperAdditiveNormalizedDescendantsIsFalse :
  round73PaperAdditiveNormalizedDescendants ≡ false
round73PaperAdditiveNormalizedDescendantsIsFalse = refl

round73PaperClayPromotionIsFalse : round73PaperClayPromotion ≡ false
round73PaperClayPromotionIsFalse = refl
