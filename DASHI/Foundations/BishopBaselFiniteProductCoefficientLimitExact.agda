module DASHI.Foundations.BishopBaselFiniteProductCoefficientLimitExact where

------------------------------------------------------------------------
-- FINITE EULER-PRODUCT COEFFICIENT -> BASEL LIMIT
--
-- The finite sine-product owner proves that its t-linear coefficient is the
-- recursively accumulated negative reciprocal-square prefix.  This module
-- embeds those coefficients into Bishop reals and proves that they converge to
-- the negative of the already-constructed Basel limit.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopBaselFiniteSineProductCoefficientExact as Finite
import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as Basel
open import DASHI.Physics.YangMills.CompactLieProofLevel

embeddedFiniteProductLinear : Nat → BishopReal.ℝ
embeddedFiniteProductLinear count =
  BishopReal._⋆
    (Finite.linear (Finite.finiteSineProductJet count))

embeddedNegativeBaselPrefix : Nat → BishopReal.ℝ
embeddedNegativeBaselPrefix count =
  BishopReal._⋆ (Finite.negativeBaselPrefix count)

finiteProductLinearIsNegativePrefix :
  ∀ count →
  BishopReal._≃_
    (embeddedFiniteProductLinear count)
    (embeddedNegativeBaselPrefix count)
finiteProductLinearIsNegativePrefix count =
  BishopP.⋆-cong
    (BishopP.≃-reflexive
      (Finite.finiteSineProductLinearIsNegativeBaselPrefix count))

negativePrefixIsNegativeBaselPartial :
  ∀ count →
  BishopReal._≃_
    (embeddedNegativeBaselPrefix count)
    (BishopReal.-
      (BishopSequence.SeriesOf Basel.baselTerm count))
negativePrefixIsNegativeBaselPartial zero =
  let open BishopP.ℝ-Solver
  in solve 0
    (Κ 0ℚᵘ ⊜ ⊝ Κ 0ℚᵘ)
    BishopP.≃-refl
negativePrefixIsNegativeBaselPartial (suc count) =
  let
    old = embeddedNegativeBaselPrefix count
    term = Basel.baselTerm count
    partial = BishopSequence.SeriesOf Basel.baselTerm count
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.≃-trans
      (BishopP.⋆-distrib-to-p⋆-q⋆
        (Finite.negativeBaselPrefix count)
        (Finite.reciprocalSquare count))
      (BishopP.+-cong
        (negativePrefixIsNegativeBaselPartial count)
        BishopP.≃-refl))
    (solve 2
      (λ p t → (⊝ p) ⊖ t ⊜ ⊝ (p ⊕ t))
      BishopP.≃-refl
      partial term)

embeddedFiniteProductLinearConvergesNegativeBasel :
  BishopSequence._ConvergesTo_
    embeddedFiniteProductLinear
    (BishopReal.- Basel.baselLimit)
embeddedFiniteProductLinearConvergesNegativeBasel =
  BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc count) →
      BishopP.≃-trans
        (finiteProductLinearIsNegativePrefix (suc count))
        (negativePrefixIsNegativeBaselPartial (suc count))})
    (BishopReal.- Basel.baselLimit ,
      BishopSequence.-xₙ→-x₀ Basel.baselSeriesConvergent)

bishopBaselFiniteProductCoefficientLimitLevel : ProofLevel
bishopBaselFiniteProductCoefficientLimitLevel = machineChecked
