module DASHI.Physics.Closure.NSAncientBlowupLpMassScaleAuditExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Authors: Gabriel Koch; Nikolai Nadirashvili; Gregory A. Seregin;
--          Vladimir Sverak.
-- Title: "Liouville theorems for the Navier-Stokes equations and applications".
-- DOI: 10.1007/s11511-009-0039-6.
--
-- PURPOSE
-- For the velocity-maximum rescaling on three spatial dimensions,
--
--   v(y) = mu u(x0 + mu y),      mu*M = 1,
--
-- the spatial Jacobian contributes M^3 while |v|^p contributes mu^p.
-- Therefore the full-domain p-mass factor is M^(3-p):
--
--   p=2 : factor M,
--   p=3 : factor 1,
--   p=4 : factor mu.
--
-- This exact audit rules out finite periodic L2 energy as a free
-- constant-excluding invariant for the ancient limit.  L3 is the critical
-- scale-invariant candidate, but a uniform L3 bound is itself a critical
-- regularity input rather than something supplied by the energy inequality.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

cube : ℚ → ℚ
cube x = x * (x * x)

l2MassScaleFactor : ℚ → ℚ → ℚ
l2MassScaleFactor mu M = (mu * mu) * cube M

l3MassScaleFactor : ℚ → ℚ → ℚ
l3MassScaleFactor mu M = cube mu * cube M

l4MassScaleFactor : ℚ → ℚ → ℚ
l4MassScaleFactor mu M = ((mu * mu) * (mu * mu)) * cube M

l2MassGrowsByBlowupAmplitude :
  (mu M : ℚ) →
  mu * M ≡ 1ℚ →
  l2MassScaleFactor mu M ≡ M
l2MassGrowsByBlowupAmplitude mu M inverseScale =
  let
    regroup : l2MassScaleFactor mu M ≡ ((mu * M) * (mu * M)) * M
    regroup = solve (mu ∷ M ∷ [])

    replaceInverse :
      ((mu * M) * (mu * M)) * M ≡ (1ℚ * 1ℚ) * M
    replaceInverse = cong (λ z → (z * z) * M) inverseScale
  in
  trans regroup
    (trans replaceInverse
      (trans (cong (_* M) (ℚP.*-identityˡ 1ℚ))
        (ℚP.*-identityˡ M)))

l3MassIsScaleInvariant :
  (mu M : ℚ) →
  mu * M ≡ 1ℚ →
  l3MassScaleFactor mu M ≡ 1ℚ
l3MassIsScaleInvariant mu M inverseScale =
  let
    regroup : l3MassScaleFactor mu M ≡ cube (mu * M)
    regroup = solve (mu ∷ M ∷ [])

    replaceInverse : cube (mu * M) ≡ cube 1ℚ
    replaceInverse = cong cube inverseScale

    cubeOne : cube 1ℚ ≡ 1ℚ
    cubeOne = solve []
  in
  trans regroup (trans replaceInverse cubeOne)

l4MassShrinksByInverseAmplitude :
  (mu M : ℚ) →
  mu * M ≡ 1ℚ →
  l4MassScaleFactor mu M ≡ mu
l4MassShrinksByInverseAmplitude mu M inverseScale =
  let
    regroup : l4MassScaleFactor mu M ≡ mu * cube (mu * M)
    regroup = solve (mu ∷ M ∷ [])

    replaceInverse : mu * cube (mu * M) ≡ mu * cube 1ℚ
    replaceInverse = cong (mu *_) (cong cube inverseScale)

    finish : mu * cube 1ℚ ≡ mu
    finish = solve (mu ∷ [])
  in
  trans regroup (trans replaceInverse finish)
