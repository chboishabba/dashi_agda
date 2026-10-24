module DASHI.Mathematics.Topology.AlexanderHornedC3MaschkeReynoldsExact where

------------------------------------------------------------------------
-- NONMODULAR C3 SEMISIMPLICITY, WITH A LITERAL REYNOLDS PROJECTOR
--
-- Original theorem: Heinrich Maschke, 1898; see Serre,
-- Linear Representations of Finite Groups, and Milne, Group
-- Theory, §7.4.  The projector is averaging by |C3|^{-1}.
--
-- IMPORTANT PREVIOUS DASHI OWNERS:
--   AlexanderHornedC3AmbientRotationExact.rotateXYZ : same R3 rotation
--   Analysis.NormalizedFibreAveragingExact : rational finite
--      fibre projector and residual; this is its 3-point owner
--   Moonshine.C3CyclotomicRealDescentExact : fixed real line
--      and irreducible rational conjugate-pair plane;
--   Moonshine.C3FourierConjugationExact : cyclotomic rows;
-- Donor provenance is kept in the source comments / roadmap, not
-- as unused imports that expand this module's kernel dependency graph.
--   Physics.Foundations.R3HodgeCrossExact : same ordered
--      R3 axes, SU2 cross/Hodge owner on an axiomatic real
--      scalar (NOT definitionally identical to Rational).
--   Wikimedia.IbrahimMonster3BWholeCharacterIsotypicBypassExact
--      cites the existing mathlib Maschke theorem.
--
-- Construct P=(I+R+R²)/3 on the ACTUAL R3 cyclic coordinate map,
-- and Q=I-P. All equality proofs are concrete rational polynomial
-- laws. This yields a direct sum of an invariant line and
-- an invariant sum-zero plane, not merely a 'semisimple=true' flag.
--
-- No claim that the char-3 reduction is semisimple, and no
-- geometric spin/Dirac zero-mode theorem is promoted.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Mathematics.Topology.AlexanderHornedC3AmbientRotationExact as R3

third : ℚ
third = + 1 / 3

RationalR3 : Set
RationalR3 = R3.Triple ℚ

zeroR3 : RationalR3
zeroR3 = R3.xyz 0ℚ 0ℚ 0ℚ

addR3 : RationalR3 → RationalR3 → RationalR3
addR3 (R3.xyz x y z) (R3.xyz u v w) =
  R3.xyz (x + u) (y + v) (z + w)

subtractR3 : RationalR3 → RationalR3 → RationalR3
subtractR3 (R3.xyz x y z) (R3.xyz u v w) =
  R3.xyz (x - u) (y - v) (z - w)

r3Ext :
  ∀ {x y z x' y' z' : ℚ} →
  x ≡ x' → y ≡ y' → z ≡ z' →
  R3.xyz x y z ≡ R3.xyz x' y' z'
r3Ext refl refl refl = refl

sumCoordinates : RationalR3 → ℚ
sumCoordinates (R3.xyz x y z) = x + y + z

mean : RationalR3 → ℚ
mean point = third * sumCoordinates point

-- Exactly the normalized finite-fibre averaging pattern already used
-- by NormalizedFibreAveragingExact, now on the real C3 orbit.
P : RationalR3 → RationalR3
P point = R3.xyz (mean point) (mean point) (mean point)

Q : RationalR3 → RationalR3
Q point = subtractR3 point (P point)

meanOfConstant : ∀ x → mean (R3.xyz x x x) ≡ x
meanOfConstant = ℚRing.solve-∀

meanAfterRotation : ∀ point →
  mean (R3.rotateXYZ point) ≡ mean point
meanAfterRotation (R3.xyz x y z) = ℚRing.solve-∀

projectorIdempotent : ∀ point → P (P point) ≡ P point
projectorIdempotent point =
  cong (λ x → R3.xyz x x x) (meanOfConstant (mean point))

projectorEquivariant : ∀ point →
  P (R3.rotateXYZ point) ≡ R3.rotateXYZ (P point)
projectorEquivariant point =
  cong (λ x → R3.xyz x x x) (meanAfterRotation point)

projectedPointFixed : ∀ point →
  R3.rotateXYZ (P point) ≡ P point
projectedPointFixed point = refl

zeroMeanOfResidual : ∀ point → mean (Q point) ≡ 0ℚ
zeroMeanOfResidual (R3.xyz x y z) = ℚRing.solve-∀

projectorKillsResidual : ∀ point → P (Q point) ≡ zeroR3
projectorKillsResidual point =
  cong (λ x → R3.xyz x x x) (zeroMeanOfResidual point)

residualKillsProjected : ∀ point → Q (P point) ≡ zeroR3
residualKillsProjected (R3.xyz x y z) =
  r3Ext ℚRing.solve-∀ ℚRing.solve-∀ ℚRing.solve-∀

residualIdempotent : ∀ point → Q (Q point) ≡ Q point
residualIdempotent (R3.xyz x y z) =
  r3Ext ℚRing.solve-∀ ℚRing.solve-∀ ℚRing.solve-∀

residualEquivariant : ∀ point →
  Q (R3.rotateXYZ point) ≡ R3.rotateXYZ (Q point)
residualEquivariant (R3.xyz x y z) =
  r3Ext ℚRing.solve-∀ ℚRing.solve-∀ ℚRing.solve-∀

projectionPlusResidual : ∀ point →
  addR3 (P point) (Q point) ≡ point
projectionPlusResidual (R3.xyz x y z) =
  r3Ext ℚRing.solve-∀ ℚRing.solve-∀ ℚRing.solve-∀

-- The two invariant summands are:
--   image(P) = diagonal C3-fixed line;
--   image(Q) = sum-zero 2-plane.
-- For every vector v, v=P(v)+Q(v), P²=P, Q²=Q, PQ=QP=0.
-- The latter algebra proves direct-sum splitting over Q.
--
-- The parent sources already record the cyclotomic rational
-- two-dimensional irreducible sector: this module pays the
-- missing SAME THREE-COORDINATE map and projector equations.
