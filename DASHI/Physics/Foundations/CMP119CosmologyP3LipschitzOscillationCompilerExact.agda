{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3LipschitzOscillationCompilerExact where

------------------------------------------------------------------------
-- S3b MAX-CUT: LIPSCHITZ CELL OSCILLATION + VANISHING MESH.
--
-- Do not ask directly for `Vanishes oscillation`.  If the literal Eq.(1.71)
-- integrand has a cutoff/slow-field fixed Lipschitz constant L on the compact
-- integration domain and the refinement cells have mesh delta_n, then choose
-- the common oscillation modulus omega_n = L delta_n.  Standard finite algebra
-- of vanishing real sequences gives omega_n -> 0.
--
-- Thus the genuine analytic/source work is reduced to:
--   (1) a literal Eq.(1.71) cell oscillation bound by L * mesh;
--   (2) a product-Haar refinement with mesh -> 0.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_)
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanRealVanishingFiniteAlgebraExact as Vanishing

record LipschitzMeshOscillationData
    (sequenceLimit : Seq.RealSequenceLimitByVanishingError)
    (vanishing : Vanishing.RealVanishingFiniteAlgebra sequenceLimit) : Set₁ where
  field
    lipschitzConstant : ℝ
    mesh : Nat → ℝ
    oscillationModulus : Nat → ℝ

    meshVanishes : Seq.Vanishes sequenceLimit mesh

    oscillationIsLipschitzMesh : ∀ refinement →
      oscillationModulus refinement
      ≡ lipschitzConstant *ℝ mesh refinement

open LipschitzMeshOscillationData public

lipschitzMeshVanishes :
  ∀ {sequenceLimit vanishing}
    (data : LipschitzMeshOscillationData sequenceLimit vanishing) →
  Seq.Vanishes sequenceLimit
    (λ refinement →
      lipschitzConstant data *ℝ mesh data refinement)
lipschitzMeshVanishes {vanishing = vanishing} data =
  Vanishing.vanishesScaleLeft vanishing
    (lipschitzConstant data) (mesh data) (meshVanishes data)

oscillationVanishes :
  ∀ {sequenceLimit vanishing}
    (data : LipschitzMeshOscillationData sequenceLimit vanishing) →
  Seq.Vanishes sequenceLimit (oscillationModulus data)
oscillationVanishes {sequenceLimit = sequenceLimit} data =
  Seq.vanishesCongruent sequenceLimit
    (λ refinement →
      lipschitzConstant data *ℝ mesh data refinement)
    (oscillationModulus data)
    (λ refinement →
      Relation.Binary.PropositionalEquality.sym
        (oscillationIsLipschitzMesh data refinement))
    (lipschitzMeshVanishes data)
  where
  import Relation.Binary.PropositionalEquality

independentOscillationVanishingTheoremRequired : Bool
independentOscillationVanishingTheoremRequired = false

remainingEquation171AnalyticWorkIsLipschitzCellBound : Bool
remainingEquation171AnalyticWorkIsLipschitzCellBound = true

remainingHaarPartitionWorkIsVanishingMesh : Bool
remainingHaarPartitionWorkIsVanishingMesh = true
