module DASHI.Analysis.RiemannPhiCoshCoercivityReductionExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Isolate the elementary real-analysis content of the diagonal Hermitian
-- kernel excess.  For the source taper
--
--   Phi(z) = integral phi(u)^2 exp(i z u) du,
--
-- real/even phi gives at z=-2 i alpha
--
--   Phi(-2 i alpha) - Phi(0)
--     = integral phi(u)^2 (cosh(2 alpha u)-1) du
--     >= 2 alpha^2 integral u^2 phi(u)^2 du.
--
-- The source also proves phi=1 on |u| <= L/2-w.  With w <= L/8 the plateau
-- radius is at least 3L/8, so the second moment is strictly positive (indeed it
-- has an explicit polynomial lower bound).  Thus this is a standard real-
-- analysis bridge, not a zeta-specific new mechanism.
--
-- We encode the exact nonnegative ledger consumed downstream.  The remaining
-- analytic formalization is to instantiate the ledger from Mathlib/source
-- integral inequalities; no new zeta arithmetic is hidden here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

------------------------------------------------------------------------
-- Exact coercivity ledger:
--
--   c_phi alpha^2 + slack = Phi(-2 i alpha)-Phi(0),
--   c_phi = 2 M2,
--   M2 > 0.
------------------------------------------------------------------------

record PhiCoshCoercivityLedger : Set where
  constructor phiCoshCoercivityLedger
  field
    alphaSquared : Nat
    secondMomentPredecessor : Nat
    phiExcess : Nat
    coshSlack : Nat

    coercivityIdentity :
      ((suc (suc 0)) * suc secondMomentPredecessor) * alphaSquared
        + coshSlack
      ≡ phiExcess

open PhiCoshCoercivityLedger public

coerciveWeight : PhiCoshCoercivityLedger → Nat
coerciveWeight l = (suc (suc 0)) * suc (secondMomentPredecessor l)

coerciveWeightIsPositiveMultipleOfTwo :
  (l : PhiCoshCoercivityLedger) →
  coerciveWeight l ≡ (suc (suc 0)) * suc (secondMomentPredecessor l)
coerciveWeightIsPositiveMultipleOfTwo l = refl

------------------------------------------------------------------------
-- Source-facing factorization of the real-analysis proof.
------------------------------------------------------------------------

record PhiImaginaryAxisCoshProducer : Set₁ where
  field
    Parameter : Set

    AlphaSquared : Parameter → Nat
    SecondMoment : Parameter → Nat
    PhiExcess : Parameter → Nat
    CoshSlack : Parameter → Nat

    phiImaginaryAxisIsCoshIntegral :
      (p : Parameter) → Set

    coshMinusOneQuadraticLowerBound :
      (p : Parameter) → Set

    taperSecondMomentPositive :
      (p : Parameter) → Set

    coercivityLedger :
      (p : Parameter) → PhiCoshCoercivityLedger

------------------------------------------------------------------------
-- Even stronger source connection: plateau positivity gives a concrete moment
-- lower-bound route.  In the actual source, phi_eq_one supplies the plateau;
-- the only missing formal arithmetic is integrating u^2 on a symmetric
-- interval and applying w <= L/8.
------------------------------------------------------------------------

record TaperPlateauSecondMomentBridge : Set₁ where
  field
    Scale : Set
    taperLength : Scale
    taperWidth : Scale
    plateauRadius : Scale
    explicitSecondMomentLowerBound : Scale

    sourcePhiEqualsOneOnPlateau : Set
    sourceWidthAtMostLengthOverEight : Set
    symmetricUSquaredIntegralComputed : Set
    lowerBoundStrictlyPositive : Set

record PhiCoshCoercivityBoundary : Set where
  field
    coshQuadraticMechanismIdentified : Bool
    coercivityWeightExplicitlyTwoSecondMoment : Bool
    sourceTaperPlateauOwned : Bool
    sourceWidthRangeOwned : Bool
    secondMomentPositivityReducedToElementaryIntegral : Bool
    coshInequalityFormalizedInDashiHere : Bool
    sourceSecondMomentBoundInstantiatedHere : Bool
    zetaSpecificArithmeticNeededForCoercivity : Bool

phiCoshCoercivityBoundary : PhiCoshCoercivityBoundary
phiCoshCoercivityBoundary = record
  { coshQuadraticMechanismIdentified = true
  ; coercivityWeightExplicitlyTwoSecondMoment = true
  ; sourceTaperPlateauOwned = true
  ; sourceWidthRangeOwned = true
  ; secondMomentPositivityReducedToElementaryIntegral = true
  ; coshInequalityFormalizedInDashiHere = false
  ; sourceSecondMomentBoundInstantiatedHere = false
  ; zetaSpecificArithmeticNeededForCoercivity = false
  }
