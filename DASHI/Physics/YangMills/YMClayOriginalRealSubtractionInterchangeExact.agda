module DASHI.Physics.YangMills.YMClayOriginalRealSubtractionInterchangeExact where

------------------------------------------------------------------------
-- Pure real subtraction interchange, derived only from the already
-- selected RealAnalysisAxioms additive laws (no new postulate).
--
-- (a - b) - (c - d) = (a - c) - (b - d).
--
-- Essential proof trick:
--   a-b = (a-c)+(c-b);
--   c-d = (b-d)+(c-b).
-- Therefore the shared middle term cancels after the exact
-- subAddDistributes law.
--
-- This removes the previously explicit scalar-ring hypothesis from
-- the original Wilson quantitative three-moment RG covariance route.
-- It remains transitive on RealAnalysisAxioms as before.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; 0ℝ; _+ℝ_; _-ℝ_;
         +-comm; +-identityʳ; subSelf;
         subAddCancelMiddle; subAddDistributes)

subtractionInterchange :
  (a b c d : ℝ) →
  ((a -ℝ b) -ℝ (c -ℝ d))
    ≡ ((a -ℝ c) -ℝ (b -ℝ d))
subtractionInterchange a b c d =
  trans
    (cong₂ _-ℝ_
      (sym (subAddCancelMiddle a c b))
      (trans
        (sym (subAddCancelMiddle c b d))
        (+-comm (c -ℝ b) (b -ℝ d))))
    (trans
      (subAddDistributes
        (a -ℝ c) (c -ℝ b) (b -ℝ d) (c -ℝ b))
      (trans
        (cong
          (λ middle →
            ((a -ℝ c) -ℝ (b -ℝ d)) +ℝ middle)
          (subSelf (c -ℝ b)))
        (+-identityʳ ((a -ℝ c) -ℝ (b -ℝ d)))))
