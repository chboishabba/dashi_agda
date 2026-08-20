module DASHI.Papers.NavierStokes.TheoremInterfaceRound72Exact where

------------------------------------------------------------------------
-- PAPER-FACING ROUND72 DELTA
--
-- PRIMARY SOURCES / CONTEXT
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
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- ROUND72 PAPER DELTA
--
-- * fixed-output resonance has one free Z^3 input, with a single-cube cubic
--   cardinality majorant; no O(N^2) surface-count shortcut is assumed;
-- * LH/HL are coded by their literal low leg and its own 2^ell cube;
-- * even optimistic O(N^2) and crude O(N^3) raw complexity produce summable
--   reciprocal shell floors and every finite prefix is explicitly fundable;
-- * four-way and eight-way branching are the exact arithmetic critical
--   multiplicities for 2^(-2j) and 2^(-3j) losses respectively;
-- * factorized Cauchy replaces raw count by physical effective complexity:
--       mu^2 <= Q W;
-- * the factorization is welded to the exact Round62 structured atom list;
-- * scalar atom values do not canonically determine Q,W, so a physical
--   velocity/Gram/energy factorization is genuinely required;
-- * the static physical shell pairing is refined back into one fine Round62
--   physical atom per triad plus Com and reconstructs the exact five-source
--   total, modulo only the explicit per-incidence HH-good/HH-bad selector.
--
-- Clay promotion remains false.  The two central physical producers are now
-- the trajectory-level effective-complexity factorization and the genuinely
-- distinct descendant multiplicity/loss theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Papers.NavierStokes.TheoremInterfaceRound71Exact
import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound72Exact as R72

round72PaperFixedOutputThreeDOF : Bool
round72PaperFixedOutputThreeDOF = R72.round72FixedOutputThreeDOFConstructed

round72PaperPolynomialFrequencyCountingNoGo : Bool
round72PaperPolynomialFrequencyCountingNoGo =
  R72.round72PolynomialFrequencyCountingNoGoConstructed

round72PaperFactorizedAmplificationConcentration : Bool
round72PaperFactorizedAmplificationConcentration =
  R72.round72FactorizedAmplificationConcentrationConstructed

round72PaperStaticFineFiveSourceConstituentList : Bool
round72PaperStaticFineFiveSourceConstituentList =
  R72.round72StaticFineFiveSourceConstituentListConstructed

round72PaperRealPolynomialPicard : Bool
round72PaperRealPolynomialPicard = R72.round72RealPolynomialLocalLipschitzAndPicard

round72PaperSelectedTrajectory : Bool
round72PaperSelectedTrajectory =
  R72.round72SelectedGalerkinTrajectoryGlobalEnergyContinuation

round72PaperDynamicPhysicalShellBalance : Bool
round72PaperDynamicPhysicalShellBalance =
  R72.round72TrajectoryInstantiatesDynamicPhysicalShellBalance

round72PaperPhysicalEffectiveComplexityFactorization : Bool
round72PaperPhysicalEffectiveComplexityFactorization =
  R72.round72CriticalAmplificationProducesPhysicalEffectiveComplexityFactorization

round72PaperDistinctDescendantMultiplicityOutrunsLoss : Bool
round72PaperDistinctDescendantMultiplicityOutrunsLoss =
  R72.round72PhysicalDistinctDescendantMultiplicityOutrunsEffectiveComplexityLoss

round72PaperCriticalRatioBarrier : Bool
round72PaperCriticalRatioBarrier = R72.round72CriticalRatioBarrierConstructed

round72PaperClayPromotion : Bool
round72PaperClayPromotion = R72.round72ClayPromotion

round72PaperFixedOutputThreeDOFIsTrue :
  round72PaperFixedOutputThreeDOF ≡ true
round72PaperFixedOutputThreeDOFIsTrue = refl

round72PaperPolynomialFrequencyCountingNoGoIsTrue :
  round72PaperPolynomialFrequencyCountingNoGo ≡ true
round72PaperPolynomialFrequencyCountingNoGoIsTrue = refl

round72PaperFactorizedAmplificationConcentrationIsTrue :
  round72PaperFactorizedAmplificationConcentration ≡ true
round72PaperFactorizedAmplificationConcentrationIsTrue = refl

round72PaperStaticFineFiveSourceConstituentListIsTrue :
  round72PaperStaticFineFiveSourceConstituentList ≡ true
round72PaperStaticFineFiveSourceConstituentListIsTrue = refl

round72PaperRealPolynomialPicardIsFalse :
  round72PaperRealPolynomialPicard ≡ false
round72PaperRealPolynomialPicardIsFalse = refl

round72PaperPhysicalEffectiveComplexityFactorizationIsFalse :
  round72PaperPhysicalEffectiveComplexityFactorization ≡ false
round72PaperPhysicalEffectiveComplexityFactorizationIsFalse = refl

round72PaperDistinctDescendantMultiplicityOutrunsLossIsFalse :
  round72PaperDistinctDescendantMultiplicityOutrunsLoss ≡ false
round72PaperDistinctDescendantMultiplicityOutrunsLossIsFalse = refl

round72PaperClayPromotionIsFalse : round72PaperClayPromotion ≡ false
round72PaperClayPromotionIsFalse = refl
