module DASHI.Physics.Gravity.KSW668F8NormalGradientConstraintSATPropagationExact where

------------------------------------------------------------------------
-- XXXIX: ORIGINAL F8 normal-gradient constraint, tensor-product
-- radial/normal commutation and G3 moving radial-shift energy weld.
--
-- Original normal_order=3 stage() at fixed T:
--   Udot=(1+v)P/2+(1-v)M/2
--   Pdot=(1+v)D_y P+F+SAT_P
--   Mdot=(v-1)D_y M+F+SAT_M
-- where F=L_r U -3(P-M)/(2z) is the SAME physical bulk force.
--
-- For Q=(P-M)/2-D_y U, with v uniform along y and SAME SBP2 D_y,
--   Qdot = (SAT_P-SAT_M)/2 EXACTLY.
-- Interior: Qdot=0.
-- Lower original weak Israel: Qdot=-(1-v)(target-M0)/dy.
-- Upper original P SAT:       Qdot=-(1+v)P_N/dy.
--
-- Original moving radial shift contribution is
-- v A_face Δ_rU Δ_r(P-M)
--  =2v A_face Δ_rU D_y(Δ_rU)
--   +2v A_face Δ_rU Δ_rQ.
-- The first term is an SBP2 normal flux/warp commutator on each
-- radial face; the second is the EXACT nonzero constraint defect
-- and cannot be silently dropped at the two SAT boundary rows.
--
-- Algebraic tensor-product Δ_r D_y=D_y Δ_r is proved for a
-- four-corner rectangle; full original outer closure, moving
-- weighted energy and SSPRK3 stability remain open.
-- Original DASHI/KSW source attribution retained; kernel NOT RUN.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

half two : ℚ
half = (+ 1) / 2
two = (+ 2) / 1

originalUdot : ℚ → ℚ → ℚ → ℚ
originalUdot v p m =
  half * ((1ℚ + v) * p + (1ℚ + - v) * m)

originalPdot : ℚ → ℚ → ℚ → ℚ → ℚ
originalPdot v dp force satP =
  (1ℚ + v) * dp + force + satP

originalMdot : ℚ → ℚ → ℚ → ℚ → ℚ
originalMdot v dm force satM =
  (v + - 1ℚ) * dm + force + satM

normalDerivativeOfUdot : ℚ → ℚ → ℚ → ℚ
normalDerivativeOfUdot v dp dm =
  half * ((1ℚ + v) * dp + (1ℚ + - v) * dm)

normalConstraintDerivative :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
normalConstraintDerivative v dp dm force satP satM =
  half * (originalPdot v dp force satP
           + - (originalMdot v dm force satM))
  + - (normalDerivativeOfUdot v dp dm)

originalNormalGradientConstraintSATOnly :
  (v dp dm force satP satM : ℚ) →
  normalConstraintDerivative v dp dm force satP satM
    ≡ half * (satP + - satM)
originalNormalGradientConstraintSATOnly
  v dp dm force satP satM = solve []

originalInteriorConstraintFrozen :
  (v dp dm force : ℚ) →
  normalConstraintDerivative v dp dm force
    ((+ 0) / 1) ((+ 0) / 1)
    ≡ (+ 0) / 1
originalInteriorConstraintFrozen v dp dm force = solve []

lowerSAT : ℚ → ℚ → ℚ → ℚ → ℚ
lowerSAT v invdy target m =
  two * (1ℚ + - v) * invdy * (target + - m)

upperSAT : ℚ → ℚ → ℚ → ℚ
upperSAT v invdy p =
  - (two * (1ℚ + v) * invdy * p)

originalLowerConstraintProduction :
  (v dp dm force invdy target m : ℚ) →
  normalConstraintDerivative v dp dm force
    ((+ 0) / 1) (lowerSAT v invdy target m)
  ≡ - ((1ℚ + - v) * invdy * (target + - m))
originalLowerConstraintProduction
  v dp dm force invdy target m = solve []

originalUpperConstraintProduction :
  (v dp dm force invdy p : ℚ) →
  normalConstraintDerivative v dp dm force
    (upperSAT v invdy p) ((+ 0) / 1)
  ≡ - ((1ℚ + v) * invdy * p)
originalUpperConstraintProduction v dp dm force invdy p = solve []

-- One radial/normal rectangular face: normal and radial first
-- differences commute, including at tensor-product boundary edges.
deltaRadialDeltaNormal :
  ℚ → ℚ → ℚ → ℚ → ℚ
deltaRadialDeltaNormal u00 u10 u01 u11 =
  (u11 + - u10) + - (u01 + - u00)

deltaNormalDeltaRadial :
  ℚ → ℚ → ℚ → ℚ → ℚ
deltaNormalDeltaRadial u00 u10 u01 u11 =
  (u11 + - u01) + - (u10 + - u00)

originalTensorProductDerivativeCommutation :
  (u00 u10 u01 u11 : ℚ) →
  deltaRadialDeltaNormal u00 u10 u01 u11
  ≡ deltaNormalDeltaRadial u00 u10 u01 u11
originalTensorProductDerivativeCommutation u00 u10 u01 u11
  = solve []

-- Δ_r W = D_y Δ_r U + Δ_r Q is the augmented original
-- compatibility equation; signed constraint defect remains explicit.
originalMovingRadialShiftConstraintDecomposition :
  (v conductance deltaU deltaUy deltaQ : ℚ) →
  two * v * conductance * deltaU * (deltaUy + deltaQ)
  ≡ two * v * conductance * deltaU * deltaUy
    + two * v * conductance * deltaU * deltaQ
originalMovingRadialShiftConstraintDecomposition
  v conductance deltaU deltaUy deltaQ = solve []
