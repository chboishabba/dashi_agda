module DASHI.Physics.YangMills.CompactLieLangevinSkewConnectionCancellationExact where

------------------------------------------------------------------------
-- ROUND72/R265: COMPACT-LIE LANGEVIN CONNECTION IS BASIS-FREE SKEW ENERGY ZERO
--               + TYPED DIFFERENTIATED-COMMUTATOR SOURCE SURFACE
--
-- GEOMETRIC SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary Introduction",
-- second edition, Graduate Texts in Mathematics 222, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
--
-- John Milnor,
-- "Curvatures of Left Invariant Metrics on Lie Groups",
-- Advances in Mathematics 21 (1976), 293--329.
-- DOI: 10.1016/S0001-8708(76)80002-3.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using (List)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.CompactLieBiInvariantSkewLangevinExact as Skew

------------------------------------------------------------------------
-- Exact basis-free cancellation inherited from the Ad-invariant metric core.
------------------------------------------------------------------------

connectionPairedEnergyCancels = Skew.connectionPairedEnergyCancels
connectionQuadraticEnergyCancels = Skew.connectionQuadraticEnergyCancels
finiteLatticeConnectionEnergyCancels = Skew.finiteLatticeConnectionEnergyCancels

compactLieSkewQuadraticCancellationLevel : ProofLevel
compactLieSkewQuadraticCancellationLevel = machineChecked

------------------------------------------------------------------------
-- Literal lattice-Langevin carrier retained for compatibility.
------------------------------------------------------------------------

record CompactLieLangevinFrameData : Set₁ where
  field
    Site Field Function : Set
    metric : Skew.BiInvariantLieMetricData
    frameDerivative : Site → Skew.Lie metric → Function → Function
    laplacian : Function → Function
    connectionDirection : Site → Field → Skew.Lie metric
    derivativeVector : Site → Field → Skew.Lie metric
    laplacianCommutesWithFrame : Set

    -- Legacy source sockets.  R265 no longer permits downstream Row-C code to
    -- treat these opaque propositions as a typed symmetric-Hessian weld.
    LangevinCommutatorIdentity : Set
    connectionIsOnsiteAdTerm : Set

open CompactLieLangevinFrameData public

literalConnectionQuadraticEnergyCancels :
  (D : CompactLieLangevinFrameData) →
  (field : Field D) →
  ∀ sites →
  Skew.sumConnectionQuadratic
    (metric D)
    (λ site → connectionDirection D site field)
    (λ site → derivativeVector D site field)
    sites
  ≡ Skew.zero (metric D)
literalConnectionQuadraticEnergyCancels D field =
  Skew.finiteLatticeConnectionEnergyCancels
    (metric D)
    (λ site → connectionDirection D site field)
    (λ site → derivativeVector D site field)

------------------------------------------------------------------------
-- R265: typed replacement for the opaque commutator producer socket.
--
-- This does not assert the Yang--Mills source theorem.  It fixes the exact data
-- a physical proof must return: the literal commutator matrix entry, its
-- symmetric nonlocal part, the connection entry, the action-Hessian entry, and
-- proof-relevant equalities between them.  A neighbouring Hessian can no longer
-- pay the source seam merely because both propositions inhabit Set.
------------------------------------------------------------------------

record TypedLangevinCommutatorData : Set₁ where
  field
    frame : CompactLieLangevinFrameData
    Coefficient : Set
    add : Coefficient → Coefficient → Coefficient

    commutatorEntry : Site frame → Site frame → Coefficient
    symmetricNonlocalEntry : Site frame → Site frame → Coefficient
    connectionEntry : Site frame → Site frame → Coefficient
    actionHessianEntry : Site frame → Site frame → Coefficient

    -- Literal differentiated generator decomposition.
    commutatorDecomposition : ∀ x y →
      commutatorEntry x y
      ≡ add (symmetricNonlocalEntry x y) (connectionEntry x y)

    -- C4b in its correctly typed form.
    symmetricNonlocalIsActionHessian : ∀ x y →
      symmetricNonlocalEntry x y ≡ actionHessianEntry x y

    -- The connection coefficient belongs to the same onsite adjoint term whose
    -- quadratic energy vanishes by the basis-free theorem above.
    connectionEntryIsOnsiteAd : Set

open TypedLangevinCommutatorData public

commutatorEntryIsHessianPlusConnection :
  (dataSet : TypedLangevinCommutatorData) →
  ∀ x y →
  commutatorEntry dataSet x y
  ≡ add dataSet
      (actionHessianEntry dataSet x y)
      (connectionEntry dataSet x y)
commutatorEntryIsHessianPlusConnection dataSet x y
  rewrite symmetricNonlocalIsActionHessian dataSet x y =
  commutatorDecomposition dataSet x y

-- The compiler above is purely typed algebra.  The physical source theorem is
-- exactly the construction of one `TypedLangevinCommutatorData` on the literal
-- finite Yang--Mills density.
typedLangevinCommutatorCompilerLevel : ProofLevel
typedLangevinCommutatorCompilerLevel = machineChecked

compactLieCasimirFrameCommutationLevel : ProofLevel
compactLieCasimirFrameCommutationLevel = standardImported

compactLieAdSkewConnectionLevel : ProofLevel
compactLieAdSkewConnectionLevel = standardImported

physicalLiteralLangevinCommutatorIdentificationLevel : ProofLevel
physicalLiteralLangevinCommutatorIdentificationLevel = conditional

typedPhysicalLiteralLangevinCommutatorInstantiationLevel : ProofLevel
typedPhysicalLiteralLangevinCommutatorInstantiationLevel = conditional
