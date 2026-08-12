module DASHI.Physics.YangMills.BalabanCMP109FederbushComponentResidualExact where

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
-- Prove the exact 3 x 3 matrix identity behind the normalized Federbush
-- perturbation.  If J is the principal-log differential and T the centre
-- trivialization transport, define
--
--   L = J-I,   S = T-I,   K = J T,   R = K-I.
--
-- Then on the literal three Lie coordinates
--
--   R = L T + S.
--
-- This is the sign/order-sensitive version of
--
--   JT-I = (J-I)T + (T-I),
--
-- proved entrywise from finite matrix multiplication.  It is shared by the
-- equation-(0.11) inverse estimate and the equation-(0.12) derivative
-- variation; no anonymous product-rule residual is permitted downstream.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational; sumRationalCong)
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact using
  (sumRationalAdd)
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanPhysicalSU2RationalMatrixCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as Jacobian

matrixCompose : Jacobian.Lie3Matrix → Jacobian.Lie3Matrix → Jacobian.Lie3Matrix
matrixCompose outer inner row column =
  sumRational Physical.lieCoordinates3
    (λ middle → outer row middle * inner middle column)

matrixComposeAddLeft : ∀ left right inner row column →
  matrixCompose (Jacobian.matrixAdd left right) inner row column
  ≡ matrixCompose left inner row column
    + matrixCompose right inner row column
matrixComposeAddLeft left right inner row column =
  trans
    (sumRationalCong Physical.lieCoordinates3 _ _
      (λ middle → ℚRing.solve-∀
        (left row middle) (right row middle) (inner middle column)))
    (sumRationalAdd Physical.lieCoordinates3
      (λ middle → left row middle * inner middle column)
      (λ middle → right row middle * inner middle column))

matrixComposeIdentityLeft : ∀ matrix row column →
  matrixCompose Jacobian.identity3 matrix row column ≡ matrix row column
matrixComposeIdentityLeft matrix row column =
  Coordinates.deltaSumIdentity
    Coordinates.lieCoordinateDecidableEquality
    Coordinates.lieCoordinatesDuplicateFree
    row
    (Jacobian.lieCoordinateComplete row)
    (λ middle → matrix middle column)

matrixComposeIdentityRight : ∀ matrix row column →
  matrixCompose matrix Jacobian.identity3 row column ≡ matrix row column
matrixComposeIdentityRight matrix row column =
  Coordinates.deltaSumIdentity
    Coordinates.lieCoordinateDecidableEquality
    Coordinates.lieCoordinatesDuplicateFree
    column
    (Jacobian.lieCoordinateComplete column)
    (matrix row)

logJacobianResidual : Jacobian.Lie3Matrix → Jacobian.Lie3Matrix
logJacobianResidual jacobian = Jacobian.matrixSubtract jacobian Jacobian.identity3

transportResidual : Jacobian.Lie3Matrix → Jacobian.Lie3Matrix
transportResidual transport = Jacobian.matrixSubtract transport Jacobian.identity3

componentJacobian : Jacobian.Lie3Matrix → Jacobian.Lie3Matrix → Jacobian.Lie3Matrix
componentJacobian = matrixCompose

componentResidual : Jacobian.Lie3Matrix → Jacobian.Lie3Matrix → Jacobian.Lie3Matrix
componentResidual jacobian transport =
  Jacobian.matrixSubtract (matrixCompose jacobian transport) Jacobian.identity3

jacobianIsIdentityPlusLogResidual : ∀ jacobian row column →
  jacobian row column
  ≡ Jacobian.identity3 row column + logJacobianResidual jacobian row column
jacobianIsIdentityPlusLogResidual jacobian row column =
  ℚRing.solve-∀ (jacobian row column) (Jacobian.identity3 row column)

transportIsIdentityPlusResidual : ∀ transport row column →
  transport row column
  ≡ Jacobian.identity3 row column + transportResidual transport row column
transportIsIdentityPlusResidual transport row column =
  ℚRing.solve-∀ (transport row column) (Jacobian.identity3 row column)

componentResidualTelescopeExact : ∀ jacobian transport row column →
  componentResidual jacobian transport row column
  ≡ matrixCompose (logJacobianResidual jacobian) transport row column
    + transportResidual transport row column
componentResidualTelescopeExact jacobian transport row column =
  let
    expandJacobian :
      matrixCompose jacobian transport row column
      ≡ matrixCompose Jacobian.identity3 transport row column
        + matrixCompose (logJacobianResidual jacobian) transport row column
    expandJacobian =
      trans
        (sumRationalCong Physical.lieCoordinates3 _ _
          (λ middle →
            cong (_* transport middle column)
              (jacobianIsIdentityPlusLogResidual jacobian row middle)))
        (sumRationalAdd Physical.lieCoordinates3
          (λ middle → Jacobian.identity3 row middle * transport middle column)
          (λ middle → logJacobianResidual jacobian row middle * transport middle column))

    identityPart = matrixComposeIdentityLeft transport row column
  in
  trans
    (cong (_- Jacobian.identity3 row column) expandJacobian)
    (trans
      (cong
        (λ value →
          (value + matrixCompose (logJacobianResidual jacobian) transport row column)
          - Jacobian.identity3 row column)
        identityPart)
      (ℚRing.solve-∀
        (transport row column)
        (matrixCompose (logJacobianResidual jacobian) transport row column)
        (Jacobian.identity3 row column)))

identityComponentResidualZero : ∀ row column →
  componentResidual Jacobian.identity3 Jacobian.identity3 row column
  ≡ 0ℚ
identityComponentResidualZero row column =
  trans
    (cong (_- Jacobian.identity3 row column)
      (matrixComposeIdentityLeft Jacobian.identity3 row column))
    (ℚRing.solve-∀ (Jacobian.identity3 row column))

componentJacobianIdentityPlusResidual : ∀ jacobian transport row column →
  componentJacobian jacobian transport row column
  ≡ Jacobian.identity3 row column
    + componentResidual jacobian transport row column
componentJacobianIdentityPlusResidual jacobian transport row column =
  ℚRing.solve-∀
    (matrixCompose jacobian transport row column)
    (Jacobian.identity3 row column)

cmp109FederbushComponentProductTelescopeLevel : ProofLevel
cmp109FederbushComponentProductTelescopeLevel = machineChecked

cmp109FederbushComponentIdentitySpecializationLevel : ProofLevel
cmp109FederbushComponentIdentitySpecializationLevel = machineChecked
