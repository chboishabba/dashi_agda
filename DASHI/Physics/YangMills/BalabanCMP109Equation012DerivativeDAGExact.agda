module DASHI.Physics.YangMills.BalabanCMP109Equation012DerivativeDAGExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Keep the derivative of printed equation (0.12) as a provenance-bearing
-- chain-rule DAG until the final flattening step.  The four leaves are
--
--   D M_source, D U_cross, D M_target^{-1}, D U_c^{-1};
--
-- they feed D RelativeProduct, then D log, D Avg, D exp and finally the
-- left multiplication by U_c.  Every edge below carries an equality between
-- the semantic derivative node and the value computed from its immediate
-- parents.  Consequently the flattened derivative cannot silently swap in a
-- separately bounded matrix.
--
-- Norm/mass estimates remain consumers of these exact nodes.  This separation
-- is deliberate: semantic chain-rule identity is proved before Schur/Frobenius
-- projection, exactly as required by the Gate-I same-object audit.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record DifferentialDAGAlgebra (Entry Base : Set) : Set₁ where
  field
    add : Entry → Entry → Entry
    zero : Entry

    relativeProductDifferential : Base → Base → Base → Base →
      Entry → Entry → Entry → Entry → Entry
    principalLogDifferential : Base → Entry → Entry
    averageDifferential : Entry → Entry
    exponentialDifferential : Base → Entry → Entry
    endpointMultiplicationDifferential : Base → Entry → Entry → Entry

open DifferentialDAGAlgebra public

record Equation012DerivativeLeaves
    {Entry Base : Set}
    (algebra : DifferentialDAGAlgebra Entry Base) : Set₁ where
  field
    sourceBase crossingBase targetBase coarseBase : Base

    sourceDerivative crossingDerivative : Entry
    targetInverseDerivative coarseInverseDerivative : Entry
    coarseDirectDerivative : Entry

open Equation012DerivativeLeaves public

record Equation012DerivativeDAG
    {Entry Base : Set}
    {algebra : DifferentialDAGAlgebra Entry Base}
    (leaves : Equation012DerivativeLeaves algebra) : Set₁ where
  field
    relativeProductDerivative : Entry
    relativeProductExact :
      relativeProductDerivative
      ≡ relativeProductDifferential algebra
          (sourceBase leaves)
          (crossingBase leaves)
          (targetBase leaves)
          (coarseBase leaves)
          (sourceDerivative leaves)
          (crossingDerivative leaves)
          (targetInverseDerivative leaves)
          (coarseInverseDerivative leaves)

    logDerivative : Entry
    logExact :
      logDerivative
      ≡ principalLogDifferential algebra
          (coarseBase leaves) relativeProductDerivative

    averagedLogDerivative : Entry
    averageExact :
      averagedLogDerivative
      ≡ averageDifferential algebra logDerivative

    exponentialDerivative : Entry
    exponentialExact :
      exponentialDerivative
      ≡ exponentialDifferential algebra
          (coarseBase leaves) averagedLogDerivative

    outputDerivative : Entry
    outputExact :
      outputDerivative
      ≡ endpointMultiplicationDifferential algebra
          (coarseBase leaves)
          (coarseDirectDerivative leaves)
          exponentialDerivative

open Equation012DerivativeDAG public

flattenedEquation012Derivative :
  ∀ {Entry Base algebra}
    {leaves : Equation012DerivativeLeaves {Entry} {Base} algebra} →
  Equation012DerivativeDAG leaves → Entry
flattenedEquation012Derivative dag =
  endpointMultiplicationDifferential _
    (coarseBase _)
    (coarseDirectDerivative _)
    (exponentialDifferential _
      (coarseBase _)
      (averageDifferential _
        (principalLogDifferential _
          (coarseBase _)
          (relativeProductDifferential _
            (sourceBase _) (crossingBase _) (targetBase _) (coarseBase _)
            (sourceDerivative _) (crossingDerivative _)
            (targetInverseDerivative _) (coarseInverseDerivative _)))))

outputDerivativeEqualsFlattenedDAG :
  ∀ {Entry Base algebra}
    {leaves : Equation012DerivativeLeaves {Entry} {Base} algebra}
    (dag : Equation012DerivativeDAG leaves) →
  outputDerivative dag ≡ flattenedEquation012Derivative dag
outputDerivativeEqualsFlattenedDAG dag =
  trans
    (outputExact dag)
    (cong
      (endpointMultiplicationDifferential _ (coarseBase _)
        (coarseDirectDerivative _))
      (trans
        (exponentialExact dag)
        (cong
          (exponentialDifferential _ (coarseBase _))
          (trans
            (averageExact dag)
            (cong
              (averageDifferential _)
              (trans
                (logExact dag)
                (cong
                  (principalLogDifferential _ (coarseBase _))
                  (relativeProductExact dag))))))))

------------------------------------------------------------------------
-- Same-object bounded node: a mass certificate is attached to the semantic
-- node itself, never to an anonymous replacement entry.
------------------------------------------------------------------------

record BoundedDerivativeNode
    {Entry Bound : Set}
    (measure : Entry → Bound)
    (entry : Entry) : Set₁ where
  field
    bound : Bound
    measuredBelowBound : Set
    semanticEntry : Entry
    semanticEntryExact : semanticEntry ≡ entry

open BoundedDerivativeNode public

record Equation012BoundedDAG
    {Entry Base Bound : Set}
    {algebra : DifferentialDAGAlgebra Entry Base}
    (measure : Entry → Bound)
    (leaves : Equation012DerivativeLeaves algebra)
    (dag : Equation012DerivativeDAG leaves) : Set₁ where
  field
    relativeNode : BoundedDerivativeNode measure (relativeProductDerivative dag)
    logNode : BoundedDerivativeNode measure (logDerivative dag)
    averageNode : BoundedDerivativeNode measure (averagedLogDerivative dag)
    exponentialNode : BoundedDerivativeNode measure (exponentialDerivative dag)
    outputNode : BoundedDerivativeNode measure (outputDerivative dag)

open Equation012BoundedDAG public

cmp109Equation012DerivativeDAGLevel : ProofLevel
cmp109Equation012DerivativeDAGLevel = machineChecked

cmp109Equation012FlattenedSameObjectLevel : ProofLevel
cmp109Equation012FlattenedSameObjectLevel = machineChecked
