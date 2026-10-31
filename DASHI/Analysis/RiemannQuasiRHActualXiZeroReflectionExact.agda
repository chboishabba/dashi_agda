module DASHI.Analysis.RiemannQuasiRHActualXiZeroReflectionExact where

-- Source math: Riemann (1859) functional equation and conjugation.
-- 2026 quasi-RH source: OpenAI 2026-09-30 7/8, separate 2026-10-05 11/12.
-- Original actual analytic carrier: RiemannAnalyticSubstrate.
-- Independent DASHI proof: derive critical-reflected nontrivial zero
-- from actual xi functional equation and conjugation semantics.
-- No external zero-free theorem is manufactured or assumed unconditionally.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)

import DASHI.Analysis.RiemannAnalyticSubstrate as A

module Actual (analytic : A.AnalyticSubstrate) where
  open A.AnalyticSubstrate analytic using (carrier; completed)
  open A.ComplexAnalyticCarrier carrier using
    (Complex; zeroC; conjC; apply; realPart)
  open A.CompletedRiemannZeta completed using
    (xi; oneMinus; isZero; nontrivialZero;
     functionalEquation; conjugationLaw;
     nontrivialZeroIsXiZero; xiZeroIsNontrivialZetaZero)

  -- The abstract CompletedRiemannZeta owner deliberately does not assert
  -- that its generic isZero predicate means "function value = zeroC".
  -- This is the minimal indispensable genuine-analytic semantics.
  record XiZeroValueSemantics : Set₁ where
    field
      zeroMeansValueZero :
        (s : Complex) → isZero xi s → apply xi s ≡ zeroC
      valueZeroMeansZero :
        (s : Complex) → apply xi s ≡ zeroC → isZero xi s
      conjugationFixesZero : conjC zeroC ≡ zeroC
  open XiZeroValueSemantics public

  criticalReflection : Complex → Complex
  criticalReflection s = conjC (oneMinus s)

  -- Full same-object analytic reflected-zero theorem: not merely the
  -- generic rational-coordinate reflection model.
  criticalReflectionPreservesNontrivialZero :
    (sem : XiZeroValueSemantics) (s : Complex) →
    nontrivialZero s → nontrivialZero (criticalReflection s)
  criticalReflectionPreservesNontrivialZero sem s zeroAtS =
    xiZeroIsNontrivialZetaZero (criticalReflection s)
      (valueZeroMeansZero sem (criticalReflection s)
        (trans (conjugationLaw (oneMinus s))
          (trans (cong conjC
                    (trans (sym (functionalEquation s))
                      (zeroMeansValueZero sem s
                        (nontrivialZeroIsXiZero s zeroAtS))))
                 (conjugationFixesZero sem))))

  -- The relevant 2026 external source theorem is an INPUT, expressed
  -- over the actual analytic zeta's nontrivial zeros and real carrier.
  record ClaimedRightZeroFree
      (rightOfBound : A.ComplexAnalyticCarrier.Real carrier → Set)
      : Set₁ where
    field
      excludesRight :
        (s : Complex) → nontrivialZero s →
        rightOfBound (realPart s) → ⊥
  open ClaimedRightZeroFree public

  -- The left side is the right-side predicate at the *genuine*
  -- reflected analytic point. Identification with Re(s)<1/8 needs
  -- the actual real-part/oneMinus/conjC arithmetic owner.
  reflectedLeftCondition :
    (rightOfBound : A.ComplexAnalyticCarrier.Real carrier → Set) →
    Complex → Set
  reflectedLeftCondition rightOfBound s =
    rightOfBound (realPart (criticalReflection s))

  sourceExclusionTransportsToLeft :
    (sem : XiZeroValueSemantics)
    (rightOfBound : A.ComplexAnalyticCarrier.Real carrier → Set)
    (source : ClaimedRightZeroFree rightOfBound)
    (s : Complex) →
    nontrivialZero s →
    reflectedLeftCondition rightOfBound s → ⊥
  sourceExclusionTransportsToLeft sem rightOfBound source s zeroAtS left =
    excludesRight source (criticalReflection s)
      (criticalReflectionPreservesNontrivialZero sem s zeroAtS)
      left
