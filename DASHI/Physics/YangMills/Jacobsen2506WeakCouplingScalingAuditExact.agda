module DASHI.Physics.YangMills.Jacobsen2506WeakCouplingScalingAuditExact where

------------------------------------------------------------------------
-- ADVERSARIAL SOURCE AUDIT
--
-- D. C. Jacobsen,
-- "A Constructive Proof of Existence and Mass Gap for Pure SU(3)
-- Yang--Mills in Four-Dimensional Space-Time", arXiv:2506.00284v1,
-- 30 May 2025.  No DOI is assigned in the supplied preprint.
--
-- The source is used here only as a lemma mine / adversarial test.  It is not
-- imported as authority for a Yang--Mills existence or mass-gap theorem.
--
-- The supplied Appendix A writes, for the plaquette activity,
--
--   |K_p| <= (3/2) beta + (9/8) beta^2,
--   beta = 6 / g0^2,
--
-- and then rewrites the right hand side as
--
--   9 g0^2 + (81/2) g0^4.
--
-- That substitution reverses the powers of g0.  The exact expression is
--
--   9 / g0^2 + (81/2) / g0^4.
--
-- Rather than depending on division cancellation, the first theorem below
-- gives a concrete weak-coupling falsifier at g0^2 = 1/100.  The displayed
-- Taylor majorant is then 405900, whereas the claimed weak-coupling expression
-- is 1881/20000 < 1.  Thus the Kotecky--Preiss small-activity conclusion in
-- that argument cannot follow from the displayed plaquette estimate.
--
-- The source also defines the five-dimensional lattice coupling
--
--   beta5 = 6 a / g5^2
--
-- and says exp(-c beta5) corrections vanish as a -> 0 at fixed g5.  Exact
-- refinement instead gives beta5(a/2) = beta5(a)/2: at fixed g5 the exponent
-- parameter shrinks under UV refinement.  No exponential implementation is
-- required to expose this direction mismatch.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _<_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSZZStrongCouplingDecisionExact as Order

weakG0Squared betaAtWeakPoint : ℚ
weakG0Squared = + 1 / 100
betaAtWeakPoint = + 600 / 1

plaquetteTaylorMajorant : ℚ → ℚ
plaquetteTaylorMajorant beta =
  (+ 3 / 2) * beta + (+ 9 / 8) * beta * beta

claimedWeakCouplingExpression : ℚ → ℚ
claimedWeakCouplingExpression gSquared =
  (+ 9 / 1) * gSquared
    + (+ 81 / 2) * gSquared * gSquared

betaAtWeakPointMatchesSixOverG2 :
  betaAtWeakPoint * weakG0Squared ≡ + 6 / 1
betaAtWeakPointMatchesSixOverG2 = ℚRing.solve []

actualTaylorMajorantAtWeakPoint :
  plaquetteTaylorMajorant betaAtWeakPoint ≡ + 405900 / 1
actualTaylorMajorantAtWeakPoint = ℚRing.solve []

claimedExpressionAtWeakPoint :
  claimedWeakCouplingExpression weakG0Squared ≡ + 1881 / 20000
claimedExpressionAtWeakPoint = ℚRing.solve []

claimedExpressionBelowOne :
  claimedWeakCouplingExpression weakG0Squared < 1ℚ
claimedExpressionBelowOne =
  subst
    (λ selected → selected < 1ℚ)
    (sym claimedExpressionAtWeakPoint)
    (Order.positiveDifferenceImpliesLess
      1ℚ (+ 1881 / 20000)
      (ℚP.positive⁻¹ (+ 18119 / 20000)))

actualTaylorMajorantAboveOne :
  1ℚ < plaquetteTaylorMajorant betaAtWeakPoint
actualTaylorMajorantAboveOne =
  subst
    (λ selected → 1ℚ < selected)
    (sym actualTaylorMajorantAtWeakPoint)
    (Order.positiveDifferenceImpliesLess
      (+ 405900 / 1) 1ℚ
      (ℚP.positive⁻¹ (+ 405899 / 1)))

claimedAndActualWeakBoundsSeparated :
  claimedWeakCouplingExpression weakG0Squared
  < plaquetteTaylorMajorant betaAtWeakPoint
claimedAndActualWeakBoundsSeparated =
  ℚP.<-trans claimedExpressionBelowOne actualTaylorMajorantAboveOne

------------------------------------------------------------------------
-- Five-dimensional scaling direction at fixed g5^2.
------------------------------------------------------------------------

beta5Numerator : ℚ → ℚ
beta5Numerator latticeSpacing = (+ 6 / 1) * latticeSpacing

halfSpacing : ℚ → ℚ
halfSpacing latticeSpacing = (+ 1 / 2) * latticeSpacing

beta5NumeratorHalvesUnderRefinement : ∀ latticeSpacing →
  beta5Numerator (halfSpacing latticeSpacing)
  ≡ (+ 1 / 2) * beta5Numerator latticeSpacing
beta5NumeratorHalvesUnderRefinement latticeSpacing =
  ℚRing.solve-∀ latticeSpacing

positiveSpacingBeta5StrictlyShrinks : ∀ latticeSpacing →
  0ℚ < latticeSpacing →
  beta5Numerator (halfSpacing latticeSpacing)
  < beta5Numerator latticeSpacing
positiveSpacingBeta5StrictlyShrinks latticeSpacing spacingPositive =
  let
    halfBeta : ℚ
    halfBeta = beta5Numerator (halfSpacing latticeSpacing)

    fullBeta : ℚ
    fullBeta = beta5Numerator latticeSpacing

    differenceExact : fullBeta - halfBeta ≡ (+ 3 / 1) * latticeSpacing
    differenceExact = ℚRing.solve-∀ latticeSpacing

    scaledPositive : 0ℚ < (+ 3 / 1) * latticeSpacing
    scaledPositive = ℚP.*-monoˡ-<-pos latticeSpacing
      (ℚP.positive⁻¹ (+ 3 / 1)) spacingPositive
  in
  Order.positiveDifferenceImpliesLess fullBeta halfBeta
    (subst (λ selected → 0ℚ < selected)
      (sym differenceExact) scaledPositive)

jacobsenWeakCouplingSubstitutionAuditLevel : ProofLevel
jacobsenWeakCouplingSubstitutionAuditLevel = machineChecked

jacobsenOrbifoldScalingDirectionAuditLevel : ProofLevel
jacobsenOrbifoldScalingDirectionAuditLevel = machineChecked

-- The audit blocks importing the supplied preprint's claimed polymer/continuum
-- theorem into the Clay route.  A corrected activity expansion and corrected
-- five-dimensional scaling argument would have to be supplied independently.
jacobsen2506ClayPromotionLevel : ProofLevel
jacobsen2506ClayPromotionLevel = conditional
