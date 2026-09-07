{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanP33ProjectedHamiltonianDomainExact where

------------------------------------------------------------------------
-- FINITE P33 PROJECTED HAMILTONIAN DOMAIN
--
-- Repository-local theorem layer.
--
-- The existing P33 physical-coordinate projector already proves, on the
-- literal 3072-coordinate rational SU(2) carrier,
--
--   P^2 = P,
--   <u,Pv> = <Pu,v>,
--   (PMP)v = P(M(Pv)),
--   symmetry(M) -> symmetry(PMP),
--   v^T(PMP)v = (Pv)^T M(Pv).
--
-- The existing physical SU(2) matrix-coercivity owner also proves that a
-- literal matrix representation of the physical Hessian inherits the P33
-- floor 1/32 on every coordinate vector.
--
-- This module packages the finite operator/domain consequence needed by the
-- M7 lane.  The operator is defined by construction as
--
--   H_P(v) = P(M(Pv)).
--
-- Hence H_P(v) lies in im(P) for every v, so the physical projected domain is
-- invariant.  On im(P), the P33 quadratic floor transports exactly to H_P.
-- The floor is deliberately NOT asserted on the whole ambient carrier, where
-- PMP can have zero modes outside im(P).
--
-- This is NOT continuum analytic self-adjointness, does not construct a dense
-- operator core, and does not identify this finite Hessian with the continuum
-- physical Yang--Mills Hamiltonian.  Those remain separate M7 payments.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact as Sq
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateProjectorExact as Projector
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2MatrixCoercivityExact as MatrixCoercivity
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33

PhysicalVector : Set
PhysicalVector = Projector.PhysicalVector

PhysicalMatrix : Set
PhysicalMatrix = Projector.PhysicalMatrix

PhysicalCoordinateMask : Set
PhysicalCoordinateMask = Projector.PhysicalCoordinateMask

record FiniteProjectedHamiltonian
    (mask : PhysicalCoordinateMask)
    (matrix : PhysicalMatrix) : Set₁ where
  field
    matrixSymmetric : ∀ left right →
      matrix left right ≡ matrix right left

open FiniteProjectedHamiltonian public

projectedHamiltonianOperator :
  ∀ {mask matrix} →
  FiniteProjectedHamiltonian mask matrix →
  PhysicalVector → PhysicalVector
projectedHamiltonianOperator {mask} {matrix} package vector =
  Projector.physicalCoordinateProject mask
    (Physical.physicalMatrixApply matrix
      (Projector.physicalCoordinateProject mask vector))

ProjectedPhysicalDomain :
  ∀ {mask matrix} →
  FiniteProjectedHamiltonian mask matrix →
  PhysicalVector → Set
ProjectedPhysicalDomain {mask} package vector =
  Projector.PhysicalConstraintProjectorImage mask vector

projectedHamiltonianMapsIntoPhysicalDomain :
  ∀ {mask matrix}
    (package : FiniteProjectedHamiltonian mask matrix)
    vector →
  ProjectedPhysicalDomain package
    (projectedHamiltonianOperator package vector)
projectedHamiltonianMapsIntoPhysicalDomain
    {mask} {matrix} package vector =
  Projector.physicalCoordinateProjectLiesInImage
    mask
    (Physical.physicalMatrixApply matrix
      (Projector.physicalCoordinateProject mask vector))

projectedHamiltonianPreservesPhysicalDomain :
  ∀ {mask matrix}
    (package : FiniteProjectedHamiltonian mask matrix)
    vector →
  ProjectedPhysicalDomain package vector →
  ProjectedPhysicalDomain package
    (projectedHamiltonianOperator package vector)
projectedHamiltonianPreservesPhysicalDomain package vector inputInDomain =
  projectedHamiltonianMapsIntoPhysicalDomain package vector

projectedHamiltonianMatrix :
  ∀ {mask matrix} →
  FiniteProjectedHamiltonian mask matrix →
  PhysicalMatrix
projectedHamiltonianMatrix {mask} {matrix} package =
  Projector.projectedPhysicalMatrix mask matrix

projectedHamiltonianMatrixRepresentsOperator :
  ∀ {mask matrix}
    (package : FiniteProjectedHamiltonian mask matrix)
    vector row →
  Physical.physicalMatrixApply
    (projectedHamiltonianMatrix package) vector row
  ≡ projectedHamiltonianOperator package vector row
projectedHamiltonianMatrixRepresentsOperator
    {mask} {matrix} package vector row =
  Projector.projectedPhysicalMatrixApplyExact
    mask matrix vector row

projectedHamiltonianMatrixSymmetric :
  ∀ {mask matrix}
    (package : FiniteProjectedHamiltonian mask matrix) →
  ∀ left right →
  projectedHamiltonianMatrix package left right
  ≡ projectedHamiltonianMatrix package right left
projectedHamiltonianMatrixSymmetric
    {mask} {matrix} package =
  Projector.projectedPhysicalMatrixSelfAdjoint
    mask matrix (matrixSymmetric package)

projectedHamiltonianQuadratic :
  ∀ {mask matrix} →
  FiniteProjectedHamiltonian mask matrix →
  PhysicalVector → ℚ
projectedHamiltonianQuadratic {mask} {matrix} package vector =
  Projector.projectedPhysicalQuadratic mask matrix vector

projectedHamiltonianQuadraticMatchesMatrix :
  ∀ {mask matrix}
    (package : FiniteProjectedHamiltonian mask matrix)
    vector →
  Physical.physicalMatrixQuadratic
    (projectedHamiltonianMatrix package) vector
  ≡ projectedHamiltonianQuadratic package vector
projectedHamiltonianQuadraticMatchesMatrix
    {mask} {matrix} package vector =
  Projector.projectedLiteralHessianMatrixRepresentsForm
    mask matrix vector

projectedNormSqExactOnPhysicalDomain :
  ∀ mask vector →
  Projector.PhysicalConstraintProjectorImage mask vector →
  Physical.physicalSU2CoordinateNormSq
    (Projector.physicalCoordinateProject mask vector)
  ≡ Physical.physicalSU2CoordinateNormSq vector
projectedNormSqExactOnPhysicalDomain mask vector image =
  Sums.sumRationalCong
    Physical.physicalSU2Coordinates4
    (λ coordinate →
      Sq.sq (Projector.physicalCoordinateProject mask vector coordinate))
    (λ coordinate → Sq.sq (vector coordinate))
    (λ coordinate →
      cong Sq.sq
        (Projector.physicalConstraintProjectorImageCharacterizationForward
          mask vector image coordinate))

record CoerciveFiniteProjectedHamiltonian
    (mask : PhysicalCoordinateMask) : Set₁ where
  field
    hessian : MatrixCoercivity.PhysicalSU2MatrixHessian
    hessianSymmetric : ∀ left right →
      MatrixCoercivity.matrix hessian left right
      ≡ MatrixCoercivity.matrix hessian right left

open CoerciveFiniteProjectedHamiltonian public

coerciveProjectedHamiltonian :
  ∀ {mask} →
  CoerciveFiniteProjectedHamiltonian mask →
  FiniteProjectedHamiltonian
    mask
    (MatrixCoercivity.matrix
      (CoerciveFiniteProjectedHamiltonian.hessian _))
coerciveProjectedHamiltonian package = record
  { matrixSymmetric = hessianSymmetric package }

projectedP33FloorOnPhysicalDomain :
  ∀ {mask}
    (package : CoerciveFiniteProjectedHamiltonian mask)
    vector →
  ProjectedPhysicalDomain
    (coerciveProjectedHamiltonian package) vector →
  P33.p33PhysicalFloor
    * Physical.physicalSU2CoordinateNormSq vector
  ≤ projectedHamiltonianQuadratic
      (coerciveProjectedHamiltonian package) vector
projectedP33FloorOnPhysicalDomain {mask} package vector image
  rewrite sym (projectedNormSqExactOnPhysicalDomain mask vector image) =
  MatrixCoercivity.physicalP33FloorTransfersToEveryCoordinate
    (hessian package)
    (Projector.physicalCoordinateProject mask vector)

record FiniteProjectedHamiltonianClosure
    {mask : PhysicalCoordinateMask}
    {matrix : PhysicalMatrix}
    (package : FiniteProjectedHamiltonian mask matrix) : Set₁ where
  field
    operator : PhysicalVector → PhysicalVector
    operatorIsProjected : operator ≡ projectedHamiltonianOperator package

    physicalDomain : PhysicalVector → Set
    physicalDomainIsProjectorImage :
      physicalDomain ≡ ProjectedPhysicalDomain package

    invariantDomain : ∀ vector →
      physicalDomain vector →
      physicalDomain (operator vector)

    matrixRepresentative : PhysicalMatrix
    matrixRepresentativeIsProjected :
      matrixRepresentative ≡ projectedHamiltonianMatrix package

    matrixRepresentativeSymmetric : ∀ left right →
      matrixRepresentative left right ≡ matrixRepresentative right left

open FiniteProjectedHamiltonianClosure public

assembleFiniteProjectedHamiltonianClosure :
  ∀ {mask matrix}
    (package : FiniteProjectedHamiltonian mask matrix) →
  FiniteProjectedHamiltonianClosure package
assembleFiniteProjectedHamiltonianClosure package = record
  { operator = projectedHamiltonianOperator package
  ; operatorIsProjected = refl
  ; physicalDomain = ProjectedPhysicalDomain package
  ; physicalDomainIsProjectorImage = refl
  ; invariantDomain = projectedHamiltonianPreservesPhysicalDomain package
  ; matrixRepresentative = projectedHamiltonianMatrix package
  ; matrixRepresentativeIsProjected = refl
  ; matrixRepresentativeSymmetric = projectedHamiltonianMatrixSymmetric package
  }

p33ProjectedHamiltonianInvariantDomainLevel : ProofLevel
p33ProjectedHamiltonianInvariantDomainLevel = machineChecked

p33ProjectedHamiltonianMatrixRepresentationLevel : ProofLevel
p33ProjectedHamiltonianMatrixRepresentationLevel = machineChecked

p33ProjectedHamiltonianFiniteSymmetryLevel : ProofLevel
p33ProjectedHamiltonianFiniteSymmetryLevel = machineChecked

p33ProjectedHamiltonianPhysicalFloorLevel : ProofLevel
p33ProjectedHamiltonianPhysicalFloorLevel = machineChecked

-- Promotion firewall.
--
-- Finite rational projected-domain invariance, symmetric matrix representation,
-- and the 1/32 floor on the projector image do not by themselves imply:
--   * a complete Hilbert carrier,
--   * a genuine unbounded operator domain,
--   * a common invariant dense operator core,
--   * analytic self-adjointness,
--   * continuum OS reconstruction,
--   * or Clay Yang--Mills promotion.
