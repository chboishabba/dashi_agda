module DASHI.Physics.Gravity.KSW668CylinderZ2WindingIsraelRationalExact where

-- Original flat double-interior-disc thin-shell example, NOT AdS5 FRW.
-- R=1, kappa5^2=1/2, T=2, f=2, n=1, compact chi=theta.
-- Copies of 5D Minkowski r<=1 glued along R^(1,2) x S1.
-- Unit normals INTO each disc; mixed extrinsic K=diag(0,-1,0,0).
-- Z2 Israel K^a_b=-(kappa5^2/2)(S^a_b - delta^a_b trace(S)/3).
-- Full winding stress mixed S=diag(-4,0,-4,-4).
-- Algebraic rational shell slice only, kernel acceptance not yet run.
open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

data Axis : Set where
  time theta u v : Axis

delta : Axis → Axis → ℚ
delta time time = 1ℚ
delta theta theta = 1ℚ
delta u u = 1ℚ
delta v v = 1ℚ
delta _ _ = 0ℚ

source : Axis → Axis → ℚ
source time time = - ((+ 4) / 1)
source theta theta = 0ℚ
source u u = - ((+ 4) / 1)
source v v = - ((+ 4) / 1)
source _ _ = 0ℚ

traceSource : ℚ
traceSource = source time time + source theta theta + source u u + source v v

traceSourceExactly : traceSource ≡ - ((+ 12) / 1)
traceSourceExactly = solve []

geometricK : Axis → Axis → ℚ
geometricK theta theta = - 1ℚ
geometricK _ _ = 0ℚ

israelFromSource : Axis → Axis → ℚ
israelFromSource a b =
  - (((+ 1) / 4) * (source a b + ((+ 4) / 1) * delta a b))

allSixteenStaticIsraelComponents :
  (a b : Axis) → geometricK a b ≡ israelFromSource a b
allSixteenStaticIsraelComponents time time = solve []
allSixteenStaticIsraelComponents time theta = solve []
allSixteenStaticIsraelComponents time u = solve []
allSixteenStaticIsraelComponents time v = solve []
allSixteenStaticIsraelComponents theta time = solve []
allSixteenStaticIsraelComponents theta theta = solve []
allSixteenStaticIsraelComponents theta u = solve []
allSixteenStaticIsraelComponents theta v = solve []
allSixteenStaticIsraelComponents u time = solve []
allSixteenStaticIsraelComponents u theta = solve []
allSixteenStaticIsraelComponents u u = solve []
allSixteenStaticIsraelComponents u v = solve []
allSixteenStaticIsraelComponents v time = solve []
allSixteenStaticIsraelComponents v theta = solve []
allSixteenStaticIsraelComponents v u = solve []
allSixteenStaticIsraelComponents v v = solve []

-- f^2 n^2/(2R^2) = T = 1/(kappa5^2 R) = 2.
originalWindingEnergyDensity : ℚ
originalWindingEnergyDensity = ((+ 4) / 2)

windingMatchesTension :
  originalWindingEnergyDensity ≡ (+ 2) / 1
windingMatchesTension = solve []
