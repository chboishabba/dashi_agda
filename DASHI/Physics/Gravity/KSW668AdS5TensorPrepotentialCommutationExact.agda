module DASHI.Physics.Gravity.KSW668AdS5TensorPrepotentialCommutationExact where

------------------------------------------------------------------------
-- Original a=t AdS5 tensor-prepotential conditional proof carrier.
--
-- L=-dT²+dz²-3/z dz+Delta_x and original Israel Neumann B
-- have coefficients independent of the three spatial brane coordinates.
-- The local fourth-order polynomial TT generator S hence commutes with
-- L and B on smooth fields by mixed-derivative commutation. The actual
-- continuum commutation witness must be supplied independently; this
-- record does NOT counterfeit a pinned Agda differential-geometry proof.
-- Source-level SymPy owner: scripts/ksw668_f8_prepotential_commutation.py.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

record OriginalAdS5TTPrepotentialContract
    (Scalar Tensor ScalarSource TensorSource : Set) : Set₁ where
  field
    scalarBulk : Scalar → Scalar
    tensorBulk : Tensor → Tensor
    scalarNeumann : Scalar → ScalarSource
    tensorNeumann : Tensor → TensorSource
    localTT : Scalar → Tensor
    sourceTT : ScalarSource → TensorSource
    zeroScalar : Scalar
    zeroTensor : Tensor
    spatialTTBulkCommutes : ∀ ψ →
      tensorBulk (localTT ψ) ≡ localTT (scalarBulk ψ)
    spatialTTNeumannCommutes : ∀ ψ →
      tensorNeumann (localTT ψ) ≡ sourceTT (scalarNeumann ψ)
    spatialTTZero : localTT zeroScalar ≡ zeroTensor

open OriginalAdS5TTPrepotentialContract public

originalAdS5TTPrepotentialBulkExact :
  ∀ {Scalar Tensor ScalarSource TensorSource}
  (dataSet : OriginalAdS5TTPrepotentialContract
    Scalar Tensor ScalarSource TensorSource)
  (ψ : Scalar) →
  scalarBulk dataSet ψ ≡ zeroScalar dataSet →
  tensorBulk dataSet (localTT dataSet ψ) ≡ zeroTensor dataSet
originalAdS5TTPrepotentialBulkExact dataSet ψ bulkZero =
  trans
    (spatialTTBulkCommutes dataSet ψ)
    (trans (cong (localTT dataSet) bulkZero)
           (spatialTTZero dataSet))

originalAdS5TTPrepotentialIsraelExact :
  ∀ {Scalar Tensor ScalarSource TensorSource}
  (dataSet : OriginalAdS5TTPrepotentialContract
    Scalar Tensor ScalarSource TensorSource)
  (ψ : Scalar) (g : ScalarSource) →
  scalarNeumann dataSet ψ ≡ g →
  tensorNeumann dataSet (localTT dataSet ψ)
    ≡ sourceTT dataSet g
originalAdS5TTPrepotentialIsraelExact dataSet ψ g sourceEquation =
  trans
    (spatialTTNeumannCommutes dataSet ψ)
    (cong (sourceTT dataSet) sourceEquation)
