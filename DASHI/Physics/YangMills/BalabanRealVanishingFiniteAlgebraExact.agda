module DASHI.Physics.YangMills.BalabanRealVanishingFiniteAlgebraExact where

------------------------------------------------------------------------
-- STANDARD FINITE ALGEBRA OF VANISHING REAL ERROR SEQUENCES
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _+ℝ_; _*ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq

record RealVanishingFiniteAlgebra
    (limitData : Seq.RealSequenceLimitByVanishingError) : Set₁ where
  field
    vanishesZero :
      Seq.Vanishes limitData (λ _ → 0ℝ)

    vanishesAdd :
      ∀ left right →
      Seq.Vanishes limitData left →
      Seq.Vanishes limitData right →
      Seq.Vanishes limitData
        (λ n → left n +ℝ right n)

    vanishesScaleLeft :
      ∀ constant sequence →
      Seq.Vanishes limitData sequence →
      Seq.Vanishes limitData
        (λ n → constant *ℝ sequence n)

    vanishesScaleRight :
      ∀ constant sequence →
      Seq.Vanishes limitData sequence →
      Seq.Vanishes limitData
        (λ n → sequence n *ℝ constant)

open RealVanishingFiniteAlgebra public

realVanishingFiniteAlgebraLevel : ProofLevel
realVanishingFiniteAlgebraLevel = standardImported
