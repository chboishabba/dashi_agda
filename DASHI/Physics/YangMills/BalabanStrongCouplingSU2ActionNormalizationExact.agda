module DASHI.Physics.YangMills.BalabanStrongCouplingSU2ActionNormalizationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks".
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Close the SU(2) action-normalization seam at the scalar quaternion level.
-- For U in SU(2) with quaternion scalar component q0(U), the fundamental real
-- trace convention is
--
--                    Re Tr(U) = 2 q0(U).
--
-- The Shen--Zhu--Zhu Gibbs exponent uses N beta Re Tr(U), hence for N=2 it is
--
--                    4 beta q0(U).
--
-- DASHI's plaquette Wilson penalty uses 1-q0(U).  With coefficient 4 beta,
--
--   4 beta q0(U) = 4 beta - 4 beta (1-q0(U)).
--
-- Thus the two finite-volume densities differ only by a configuration-
-- independent factor per plaquette, absorbed by the partition function.  The
-- second variations have opposite signs because one object is the Gibbs
-- exponent and the other is the positive action penalty.
--
-- This identifies beta's action normalization for the existing rational
-- quaternion convention.  It does not identify beta with the small-field
-- radius rho and does not construct the stochastic measure.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _-_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q

su2FundamentalRealTrace : Q.RationalQuaternion → ℚ
su2FundamentalRealTrace value = (+ 2 / 1) * Q.q0 value

shenZhuZhuSU2PlaquetteExponent : ℚ → Q.RationalQuaternion → ℚ
shenZhuZhuSU2PlaquetteExponent beta value =
  (+ 2 / 1) * beta * su2FundamentalRealTrace value

dashiSU2WilsonPenalty : ℚ → Q.RationalQuaternion → ℚ
dashiSU2WilsonPenalty beta value =
  (+ 4 / 1) * beta * (1ℚ - Q.q0 value)

su2ExponentIsConstantMinusWilsonPenalty :
  ∀ beta value →
  shenZhuZhuSU2PlaquetteExponent beta value
  ≡ (+ 4 / 1) * beta - dashiSU2WilsonPenalty beta value
su2ExponentIsConstantMinusWilsonPenalty beta value =
  solve (beta ∷ Q.q0 value ∷ [])

su2ActionCoefficientFromPaperBeta : ℚ → ℚ
su2ActionCoefficientFromPaperBeta beta = (+ 4 / 1) * beta

configuredInteriorActionCoefficientExact :
  su2ActionCoefficientFromPaperBeta (+ 1 / 96) ≡ + 1 / 24
configuredInteriorActionCoefficientExact = solve []

paperExponentSecondVariation : ℚ → ℚ → ℚ
paperExponentSecondVariation beta scalarSecondJet =
  (+ 4 / 1) * beta * scalarSecondJet

wilsonPenaltySecondVariation : ℚ → ℚ → ℚ
wilsonPenaltySecondVariation beta scalarSecondJet =
  - ((+ 4 / 1) * beta * scalarSecondJet)

exponentAndPenaltySecondVariationsOppose :
  ∀ beta scalarSecondJet →
  paperExponentSecondVariation beta scalarSecondJet
  ≡ - wilsonPenaltySecondVariation beta scalarSecondJet
exponentAndPenaltySecondVariationsOppose beta scalarSecondJet =
  solve (beta ∷ scalarSecondJet ∷ [])
