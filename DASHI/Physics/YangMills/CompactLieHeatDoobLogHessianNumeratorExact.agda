module DASHI.Physics.YangMills.CompactLieHeatDoobLogHessianNumeratorExact where

------------------------------------------------------------------------
-- ROUND74: DENOMINATOR-CLEARED HEAT/DOOB HESSIAN TARGET
--
-- STANDARD CALCULUS
--
-- Let u > 0 and V = -log u on a Riemannian manifold.  For every tangent X,
--
--   Hess V(X,X)
--     = ((X u)^2 - u Hess u(X,X)) / u^2.
--
-- Therefore a lower bound
--
--   Hess V(X,X) >= - eta |X|^2
--
-- is EQUIVALENT (because u^2 > 0) to the division-free inequality
--
--   (X u)^2 - u Hess u(X,X) + eta u^2 |X|^2 >= 0.
--
-- In the group heat/Doob lane
--
--   u_t = H_t(exp(-V_0)),        V_t = -log u_t,
--
-- heat positivity gives u_t > 0.  Thus the true Yang--Mills curvature leaf can
-- be formulated without logarithmic derivatives or division: prove the
-- numerator inequality above uniformly in cutoff, lattice volume, heat time,
-- configuration and tangent direction, with eta_t having bounded cumulative
-- integral.  `CompactLieHeatDoobRicciReserveDebtExact` then turns that debt
-- bound into an LSI using the positive compact-simple Ricci reserve.
--
-- This formulation is deliberately closer to heat-kernel estimates and easier
-- to formalize in exact ordered-ring arithmetic than an inequality containing
-- 1/u_t^2.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

record HeatLogHessianNumeratorData : Set₁ where
  field
    Time Configuration Tangent Scalar : Set

    zero : Scalar
    add multiply square : Scalar → Scalar → Scalar
    LessEqual StrictLess : Scalar → Scalar → Set

    u : Time → Configuration → Scalar
    directionalU : Time → Configuration → Tangent → Scalar
    hessianU : Time → Configuration → Tangent → Scalar
    tangentNormSq : Tangent → Scalar
    negativeHessianRate : Time → Scalar

    heatStrictlyPositive : ∀ t configuration →
      StrictLess zero (u t configuration)

    numerator : Time → Configuration → Tangent → Scalar
    numeratorDefinition : ∀ t configuration X →
      numerator t configuration X
      ≡
      add
        (add
          (square (directionalU t configuration X)
                  (directionalU t configuration X))
          (multiply (negate (u t configuration))
                    (hessianU t configuration X)))
        (multiply
          (multiply (negativeHessianRate t)
                    (square (u t configuration) (u t configuration)))
          (tangentNormSq X))

    negate : Scalar → Scalar

    numeratorNonnegative : ∀ t configuration X →
      LessEqual zero (numerator t configuration X)

open HeatLogHessianNumeratorData public

-- Exact standard-calculus bridge.  It is separated from the physical theorem
-- because the only Yang--Mills-specific content is `numeratorNonnegative` and
-- the subsequent cumulative bound on `negativeHessianRate`.
record LogHessianDebtConclusion (D : HeatLogHessianNumeratorData) : Set₁ where
  field
    HessianDebtBound : Set
    numeratorImpliesHessianDebt :
      (∀ t configuration X → LessEqual D (zero D) (numerator D t configuration X)) →
      HessianDebtBound

open LogHessianDebtConclusion public

heatPositiveLogHessianNumeratorIdentityLevel : ProofLevel
heatPositiveLogHessianNumeratorIdentityLevel = standardImported

denominatorClearedHessianDebtBridgeLevel : ProofLevel
denominatorClearedHessianDebtBridgeLevel = standardImported

-- TRUE PHYSICAL POINTWISE LEAF: bound this explicit numerator on the same
-- heat-renormalised Yang--Mills density.  No separate log-Hessian estimate is
-- required after it.
physicalYMHeatLogHessianNumeratorLevel : ProofLevel
physicalYMHeatLogHessianNumeratorLevel = conditional
