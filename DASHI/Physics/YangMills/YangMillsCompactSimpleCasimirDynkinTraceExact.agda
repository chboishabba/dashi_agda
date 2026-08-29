module DASHI.Physics.YangMills.YangMillsCompactSimpleCasimirDynkinTraceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Anthony W. Knapp,
-- "Lie Groups Beyond an Introduction", second edition, Birkhauser, 2002.
-- DOI: 10.1007/978-1-4757-2453-0.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Make the representation-normalization invariant behind the generic-G
-- one-loop colour contraction explicit on finite carriers.  For generator
-- matrices T_a on a representation basis i, suppose the same triple sum obeys
--
--   sum_a sum_j T_a(i,j) T_a(j,i) = C_R              for every i,
--
-- and
--
--   sum_i sum_j T_a(i,j) T_a(j,i) = I_R              for every a.
--
-- Finite Fubini then proves, without choosing a classification table,
--
--   (# representation basis) C_R = (# Lie generators) I_R.
--
-- This is the cross-multiplied dimension/Casimir/Dynkin-index identity.  In
-- pure Yang--Mills the Faddeev--Popov ghosts are adjoint-valued, so the adjoint
-- representation has the same finite basis cardinality as the Lie algebra;
-- the colour normalization can therefore be carried by either C_A or I_A
-- once that common normalization is fixed.  No matter representation is
-- introduced into the Clay route.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _+_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini

finiteCount : ∀ {Index : Set} → List Index → ℚ
finiteCount indices = Sums.sumRational indices (λ _ → 1ℚ)

sumConstant :
  ∀ {Index : Set} (indices : List Index) constant →
  Sums.sumRational indices (λ _ → constant)
  ≡ finiteCount indices * constant
sumConstant [] constant = refl
sumConstant (index ∷ indices) constant
  rewrite sumConstant indices constant =
  ℚRing.solve-∀ constant (finiteCount indices)

record FiniteRepresentationTraceData
    (Generator Basis : Set) : Set₁ where
  field
    generators : List Generator
    basis : List Basis
    matrix : Generator → Basis → Basis → ℚ
    casimir dynkinIndex : ℚ

    casimirDiagonal : ∀ row →
      Sums.sumRational generators
        (λ generator →
          Sums.sumRational basis
            (λ middle →
              matrix generator row middle * matrix generator middle row))
      ≡ casimir

    dynkinTraceDiagonal : ∀ generator →
      Sums.sumRational basis
        (λ row →
          Sums.sumRational basis
            (λ middle →
              matrix generator row middle * matrix generator middle row))
      ≡ dynkinIndex

open FiniteRepresentationTraceData public

tripleTraceByRepresentation :
  ∀ {Generator Basis}
    (dataSet : FiniteRepresentationTraceData Generator Basis) →
  Sums.sumRational (basis dataSet)
    (λ row →
      Sums.sumRational (generators dataSet)
        (λ generator →
          Sums.sumRational (basis dataSet)
            (λ middle →
              matrix dataSet generator row middle
                * matrix dataSet generator middle row)))
  ≡ finiteCount (basis dataSet) * casimir dataSet
tripleTraceByRepresentation dataSet =
  trans
    (Sums.sumRationalCong (basis dataSet) _ _
      (casimirDiagonal dataSet))
    (sumConstant (basis dataSet) (casimir dataSet))

tripleTraceSwapGeneratorRow :
  ∀ {Generator Basis}
    (dataSet : FiniteRepresentationTraceData Generator Basis) →
  Sums.sumRational (basis dataSet)
    (λ row →
      Sums.sumRational (generators dataSet)
        (λ generator →
          Sums.sumRational (basis dataSet)
            (λ middle →
              matrix dataSet generator row middle
                * matrix dataSet generator middle row)))
  ≡ Sums.sumRational (generators dataSet)
      (λ generator →
        Sums.sumRational (basis dataSet)
          (λ row →
            Sums.sumRational (basis dataSet)
              (λ middle →
                matrix dataSet generator row middle
                  * matrix dataSet generator middle row)))
tripleTraceSwapGeneratorRow dataSet =
  Fubini.sumSwap
    (basis dataSet) (generators dataSet)
    (λ row generator →
      Sums.sumRational (basis dataSet)
        (λ middle →
          matrix dataSet generator row middle
            * matrix dataSet generator middle row))

tripleTraceByGenerators :
  ∀ {Generator Basis}
    (dataSet : FiniteRepresentationTraceData Generator Basis) →
  Sums.sumRational (generators dataSet)
    (λ generator →
      Sums.sumRational (basis dataSet)
        (λ row →
          Sums.sumRational (basis dataSet)
            (λ middle →
              matrix dataSet generator row middle
                * matrix dataSet generator middle row)))
  ≡ finiteCount (generators dataSet) * dynkinIndex dataSet
tripleTraceByGenerators dataSet =
  trans
    (Sums.sumRationalCong (generators dataSet) _ _
      (dynkinTraceDiagonal dataSet))
    (sumConstant (generators dataSet) (dynkinIndex dataSet))

casimirDynkinDimensionBalance :
  ∀ {Generator Basis}
    (dataSet : FiniteRepresentationTraceData Generator Basis) →
  finiteCount (basis dataSet) * casimir dataSet
  ≡ finiteCount (generators dataSet) * dynkinIndex dataSet
casimirDynkinDimensionBalance dataSet =
  trans
    (sym (tripleTraceByRepresentation dataSet))
    (trans
      (tripleTraceSwapGeneratorRow dataSet)
      (tripleTraceByGenerators dataSet))

adjointCasimirDynkinSameDimensionBalance :
  ∀ {Generator Basis}
    (dataSet : FiniteRepresentationTraceData Generator Basis) →
  finiteCount (basis dataSet) ≡ finiteCount (generators dataSet) →
  finiteCount (generators dataSet) * casimir dataSet
  ≡ finiteCount (generators dataSet) * dynkinIndex dataSet
adjointCasimirDynkinSameDimensionBalance dataSet sameDimension =
  trans
    (cong (_* casimir dataSet) (sym sameDimension))
    (casimirDynkinDimensionBalance dataSet)

compactSimpleFiniteCasimirDynkinTraceBalanceLevel : ProofLevel
compactSimpleFiniteCasimirDynkinTraceBalanceLevel = machineChecked

compactSimpleAdjointIndexCasimirNormalizationLevel : ProofLevel
compactSimpleAdjointIndexCasimirNormalizationLevel = machineChecked

-- Group-specific evaluation of C_A/I_A, root data and the analytic constants
-- remains part of the compact-simple-G promotion theorem.  This file removes
-- only the representation-normalization algebra from that frontier.
