module DASHI.Physics.YangMills.BalabanClayGate4FiniteHolonomyDerivativeNormExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4FiniteHolonomyDerivativeExact as Holonomy

------------------------------------------------------------------------
-- Path-length norm bound for the exact holonomy derivative.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Michael Creutz,
-- "Quarks, Gluons and Lattices", Cambridge University Press (1983;
-- reissued 2023). DOI: 10.1017/9781009290395.
--
-- The left-trivialized derivative is a sum of one variation per path edge,
-- conjugated by prefix holonomies.  For a compact group with an Ad-invariant
-- Lie-algebra norm, every conjugation is an isometry.  Hence
--
--   ||D Hol_P[A]|| <= |P| sup_e ||A_e||.
--
-- This supplies the path stage of the CMP109 four-factor entry-norm pipeline;
-- only the concrete norm and per-edge variation bound remain physical.
------------------------------------------------------------------------

record OrderedNormAdditiveAlgebra
    (Scalar : Set) : Set₁ where
  field
    zeroScalar : Scalar
    addScalar : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    addMonotone : ∀ {left lower right upper} →
      LessEqual left lower → LessEqual right upper →
      LessEqual (addScalar left right) (addScalar lower upper)

open OrderedNormAdditiveAlgebra public

natScale :
  ∀ {Scalar} → OrderedNormAdditiveAlgebra Scalar → Nat → Scalar → Scalar
natScale algebra zero bound = zeroScalar algebra
natScale algebra (suc count) bound =
  addScalar algebra bound (natScale algebra count bound)

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ values) = suc (listLength values)

record HolonomyDerivativeNormData
    (Edge Group Lie Scalar : Set) : Set₁ where
  field
    differential : Holonomy.HolonomyDifferentialAlgebra Group Lie
    scalar : OrderedNormAdditiveAlgebra Scalar

    field : Edge → Group
    variation : Edge → Lie
    variationBound : Scalar

    norm : Lie → Scalar

    normZero :
      norm (Holonomy.zeroLie differential)
      ≡ zeroScalar scalar

    normTriangle : ∀ left right →
      LessEqual scalar
        (norm (Holonomy.addLie differential left right))
        (addScalar scalar (norm left) (norm right))

    adjointIsometry : ∀ group vector →
      norm (Holonomy.adjoint differential group vector) ≡ norm vector

    everyVariationBounded : ∀ edge →
      LessEqual scalar (norm (variation edge)) variationBound

open HolonomyDerivativeNormData public

finiteHolonomyDerivativeNormBelowPathLength :
  ∀ {Edge Group Lie Scalar}
    (dataSet : HolonomyDerivativeNormData Edge Group Lie Scalar)
    edges →
  LessEqual (scalar dataSet)
    (norm dataSet
      (Holonomy.leftTrivializedHolonomyDerivative
        (differential dataSet)
        (field dataSet)
        (variation dataSet)
        edges))
    (natScale (scalar dataSet)
      (listLength edges) (variationBound dataSet))
finiteHolonomyDerivativeNormBelowPathLength dataSet [] =
  subst
    (λ lower →
      LessEqual (scalar dataSet) lower
        (zeroScalar (scalar dataSet)))
    (sym (normZero dataSet))
    (reflexive (scalar dataSet) (zeroScalar (scalar dataSet)))
finiteHolonomyDerivativeNormBelowPathLength dataSet (edge ∷ edges) =
  transitive (scalar dataSet)
    (normTriangle dataSet
      (variation dataSet edge)
      (Holonomy.adjoint (differential dataSet)
        (field dataSet edge)
        (Holonomy.leftTrivializedHolonomyDerivative
          (differential dataSet)
          (field dataSet)
          (variation dataSet)
          edges)))
    (addMonotone (scalar dataSet)
      (everyVariationBounded dataSet edge)
      (subst
        (λ lower →
          LessEqual (scalar dataSet) lower
            (natScale (scalar dataSet)
              (listLength edges) (variationBound dataSet)))
        (sym
          (adjointIsometry dataSet
            (field dataSet edge)
            (Holonomy.leftTrivializedHolonomyDerivative
              (differential dataSet)
              (field dataSet)
              (variation dataSet)
              edges)))
        (finiteHolonomyDerivativeNormBelowPathLength dataSet edges)))

finiteHolonomyDerivativePathLengthBoundLevel : ProofLevel
finiteHolonomyDerivativePathLengthBoundLevel = machineChecked

physicalAdInvariantLieNormInputsLevel : ProofLevel
physicalAdInvariantLieNormInputsLevel = conditional

physicalPerEdgeVariationNormInputsLevel : ProofLevel
physicalPerEdgeVariationNormInputsLevel = conditional
