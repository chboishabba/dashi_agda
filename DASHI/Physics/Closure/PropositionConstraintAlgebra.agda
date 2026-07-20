module DASHI.Physics.Closure.PropositionConstraintAlgebra where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.String using (String)

open import DASHI.Unified.GRQuantumProofTerms using
  (ConstraintAlgebraProof; ConstraintAlgebraClosed)

------------------------------------------------------------------------
-- Full proposition-level hypersurface-deformation algebra.

record HypersurfaceDeformationAlgebra : Set₁ where
  field
    Operator : Set
    Lapse : Set
    Shift : Set
    SpatialMetric : Set

    Hamiltonian : Lapse → Operator
    Momentum : Shift → Operator
    bracket : Operator → Operator → Operator

    shiftBracket : Shift → Shift → Shift
    lapseDraggedByShift : Shift → Lapse → Lapse
    metricStructureShift :
      SpatialMetric → Lapse → Lapse → Shift

    spatialMetric : SpatialMetric

    momentumMomentumLaw :
      (left right : Shift) →
      bracket (Momentum left) (Momentum right)
      ≡ Momentum (shiftBracket left right)

    momentumHamiltonianLaw :
      (shift : Shift) (lapse : Lapse) →
      bracket (Momentum shift) (Hamiltonian lapse)
      ≡ Hamiltonian (lapseDraggedByShift shift lapse)

    hamiltonianHamiltonianLaw :
      (left right : Lapse) →
      bracket (Hamiltonian left) (Hamiltonian right)
      ≡ Momentum (metricStructureShift spatialMetric left right)

record QuantumConstraintRepresentation
  (classical : HypersurfaceDeformationAlgebra) : Set₁ where
  field
    HilbertState : Set
    represent :
      HypersurfaceDeformationAlgebra.Operator classical →
      HilbertState → HilbertState
    physicalState : HilbertState → Set

    representationRespectsMomentumMomentum : Set
    representationRespectsMomentumHamiltonian : Set
    representationRespectsHamiltonianHamiltonian : Set
    noCentralAnomaly : Set
    decimationCommutesWithCausalRelabelling : Set

    representationRespectsMomentumMomentumProof :
      representationRespectsMomentumMomentum
    representationRespectsMomentumHamiltonianProof :
      representationRespectsMomentumHamiltonian
    representationRespectsHamiltonianHamiltonianProof :
      representationRespectsHamiltonianHamiltonian
    noCentralAnomalyProof : noCentralAnomaly
    decimationCommutesWithCausalRelabellingProof :
      decimationCommutesWithCausalRelabelling

------------------------------------------------------------------------
-- Exact trivial/flat producer.

flatHDA : HypersurfaceDeformationAlgebra
flatHDA =
  record
    { Operator = ⊤
    ; Lapse = ⊤
    ; Shift = ⊤
    ; SpatialMetric = ⊤
    ; Hamiltonian = λ _ → tt
    ; Momentum = λ _ → tt
    ; bracket = λ _ _ → tt
    ; shiftBracket = λ _ _ → tt
    ; lapseDraggedByShift = λ _ _ → tt
    ; metricStructureShift = λ _ _ _ → tt
    ; spatialMetric = tt
    ; momentumMomentumLaw = λ _ _ → refl
    ; momentumHamiltonianLaw = λ _ _ → refl
    ; hamiltonianHamiltonianLaw = λ _ _ → refl
    }

flatQuantumConstraintRepresentation : QuantumConstraintRepresentation flatHDA
flatQuantumConstraintRepresentation =
  record
    { HilbertState = ⊤
    ; represent = λ _ _ → tt
    ; physicalState = λ _ → ⊤
    ; representationRespectsMomentumMomentum = tt ≡ tt
    ; representationRespectsMomentumHamiltonian = tt ≡ tt
    ; representationRespectsHamiltonianHamiltonian = tt ≡ tt
    ; noCentralAnomaly = tt ≡ tt
    ; decimationCommutesWithCausalRelabelling = tt ≡ tt
    ; representationRespectsMomentumMomentumProof = refl
    ; representationRespectsMomentumHamiltonianProof = refl
    ; representationRespectsHamiltonianHamiltonianProof = refl
    ; noCentralAnomalyProof = refl
    ; decimationCommutesWithCausalRelabellingProof = refl
    }

flatConstraintSurface : ConstraintAlgebraProof
flatConstraintSurface =
  record
    { Operator = ⊤
    ; Lapse = ⊤
    ; Shift = ⊤
    ; Hamiltonian = λ _ → tt
    ; Momentum = λ _ → tt
    ; bracket = λ _ _ → tt
    ; momentumMomentumClosure = tt ≡ tt
    ; momentumHamiltonianClosure = tt ≡ tt
    ; hamiltonianHamiltonianClosure = tt ≡ tt
    ; metricDependentStructureFunctions = tt ≡ tt
    ; decimationRelabellingEquivariance = tt ≡ tt
    ; anomalyFreeQuantumRepresentation = tt ≡ tt
    }

flatConstraintClosed : ConstraintAlgebraClosed flatConstraintSurface
flatConstraintClosed =
  record
    { momentumMomentumClosureProof = refl
    ; momentumHamiltonianClosureProof = refl
    ; hamiltonianHamiltonianClosureProof = refl
    ; metricDependentStructureFunctionsProof = refl
    ; decimationRelabellingEquivarianceProof = refl
    ; anomalyFreeQuantumRepresentationProof = refl
    }

constraintBoundaryText : String
constraintBoundaryText =
  "The full hypersurface-deformation law is now an equality-level interface with a separate quantum anomaly record.  The canonical inhabitant is the exact trivial flat model only; nontrivial metric structure functions and physical quantum closure require a separate producer."
