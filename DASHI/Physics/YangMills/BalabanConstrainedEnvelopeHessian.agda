module DASHI.Physics.YangMills.BalabanConstrainedEnvelopeHessian where

-- Algebraic closure of the nested constrained-minimum Hessian formula.
--
-- Once differentiation of the source variational problem supplies the
-- linearised KKT system and the envelope identity
--
--   D²F_coarse = dλ,
--
-- uniqueness of the KKT multiplier derivative proves
--
--   D²F_coarse = (Q L^{-1} Q*)^{-1}.
--
-- The source-specific burden remains identifying the literal constrained-
-- Lagrangian Hessian L, including the constraint-curvature and gauge terms.

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.BalabanNestedConstraintMinimum using
  ( _∘_
  ; _≈_
  ; constrainedCovariance
  ; trans
  )
open import DASHI.Physics.YangMills.BalabanConstrainedKKTLinearisation using
  ( identity
  ; multiplierDerivative
  ; LinearisedKKTSystem
  ; linearisedKKTMultiplierUnique
  )

-- Pointwise equality is transitive in the direction needed below.
pointwiseTrans :
  {A B : Set} →
  {f g h : A → B} →
  f ≈ g →
  g ≈ h →
  f ≈ h
pointwiseTrans f≈g g≈h x = trans (f≈g x) (g≈h x)

constrainedEnvelopeHessian :
  {Fine Coarse : Set} →
  (L inverseL : Fine → Fine) →
  (Q : Fine → Coarse) →
  (Q* : Coarse → Fine) →
  (coarseSchur : Coarse → Coarse) →
  (fineLeftInverse : inverseL ∘ L ≈ identity) →
  (coarseLeftInverse :
    coarseSchur ∘ constrainedCovariance Q inverseL Q*
      ≈ identity) →
  (db : Coarse → Fine) →
  (dλ : Coarse → Coarse) →
  LinearisedKKTSystem L Q Q* db dλ →
  (envelopeHessian : Coarse → Coarse) →
  envelopeHessian ≈ dλ →
  envelopeHessian ≈ multiplierDerivative coarseSchur
constrainedEnvelopeHessian
  L inverseL Q Q* coarseSchur
  fineLeftInverse coarseLeftInverse
  db dλ system envelopeHessian envelopeIdentity =
  pointwiseTrans
    envelopeIdentity
    (linearisedKKTMultiplierUnique
      L inverseL Q Q* coarseSchur
      fineLeftInverse coarseLeftInverse
      db dλ system)

-- The literal inverse implementation may be substituted directly.
constructedConstrainedEnvelopeHessian :
  {Fine Coarse : Set} →
  (L inverseL : Fine → Fine) →
  (Q : Fine → Coarse) →
  (Q* : Coarse → Fine) →
  (inverseCoarse :
    (Coarse → Coarse) →
    Coarse → Coarse) →
  (fineLeftInverse : inverseL ∘ L ≈ identity) →
  (coarseLeftInverse :
    inverseCoarse (constrainedCovariance Q inverseL Q*)
      ∘ constrainedCovariance Q inverseL Q*
      ≈ identity) →
  (db : Coarse → Fine) →
  (dλ : Coarse → Coarse) →
  LinearisedKKTSystem L Q Q* db dλ →
  (envelopeHessian : Coarse → Coarse) →
  envelopeHessian ≈ dλ →
  envelopeHessian
    ≈ inverseCoarse (constrainedCovariance Q inverseL Q*)
constructedConstrainedEnvelopeHessian
  L inverseL Q Q* inverseCoarse
  fineLeftInverse coarseLeftInverse
  db dλ system envelopeHessian envelopeIdentity =
  constrainedEnvelopeHessian
    L inverseL Q Q*
    (inverseCoarse (constrainedCovariance Q inverseL Q*))
    fineLeftInverse coarseLeftInverse
    db dλ system envelopeHessian envelopeIdentity
