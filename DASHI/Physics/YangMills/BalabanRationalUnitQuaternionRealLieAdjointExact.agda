{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanRationalUnitQuaternionRealLieAdjointExact where

------------------------------------------------------------------------
-- RATIONAL UNIT QUATERNION -> REAL SU(2) LIE ADJOINT
--
-- The exact periodic Path13 realization stores links as RationalUnitQuaternion,
-- while the strongest Eq.(119) Lie calculus uses the literal real
-- `SU2LieAlgebra`.  Rather than postulating a group embedding, erase the unit
-- quaternion to the already-owned rational quaternion, form the literal 3x3
-- adjoint matrix on the rational Lie basis, and use R210's canonical real
-- matrix extension.
--
-- Thus the only scalar interface is the pre-existing R208
-- `RationalRealRingEmbedding`.  No new group law or adjoint axiom is added.
------------------------------------------------------------------------

open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.BalabanCMP98SelectedPhysicalUnitCarrierRound187Exact as R187
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as Jacobian
import DASHI.Physics.YangMills.BalabanPath13BackgroundGaugeAdjointDefectExact as Background
import DASHI.Physics.YangMills.BalabanP33QuaternionAdjointPerturbationExact as Adjoint
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as R208
import DASHI.Physics.YangMills.BalabanFederbushCanonicalRealMatrixExtensionRound210Exact as R210
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie

unitAdjointRationalMatrix :
  SU2.RationalUnitQuaternion → Jacobian.Lie3Matrix
unitAdjointRationalMatrix unit row column =
  Background.quaternionCoordinate row
    (Adjoint.adjointTransport
      (R187.eraseUnitQuaternion unit)
      (Background.basisQuaternion column))

unitAdjointRationalMatrixEntryExact :
  ∀ unit row column →
  unitAdjointRationalMatrix unit row column
  ≡ Background.quaternionCoordinate row
      (Adjoint.adjointTransport
        (R187.eraseUnitQuaternion unit)
        (Background.basisQuaternion column))
unitAdjointRationalMatrixEntryExact unit row column = Agda.Builtin.Equality.refl

unitAdjointRealLie :
  R208.RationalRealRingEmbedding →
  SU2.RationalUnitQuaternion →
  Lie.SU2LieAlgebra → Lie.SU2LieAlgebra
unitAdjointRealLie embedding unit =
  R210.canonicalRealMatrixExtension
    embedding (unitAdjointRationalMatrix unit)

unitAdjointRealLieCoordinateExact :
  ∀ embedding unit vector coordinate →
  DASHI.Physics.YangMills.BalabanFederbushRationalLieToRealSU2CarrierRound207Exact.realLieCoordinate
    coordinate (unitAdjointRealLie embedding unit vector)
  ≡ R210.realMatrixAction embedding
      (unitAdjointRationalMatrix unit) vector coordinate
unitAdjointRealLieCoordinateExact embedding unit vector coordinate =
  R210.canonicalRealMatrixExtensionCoordinateExact
    embedding (unitAdjointRationalMatrix unit) vector coordinate

rationalUnitQuaternionRealLieAdjointCompilerLevel : ProofLevel
rationalUnitQuaternionRealLieAdjointCompilerLevel = machineChecked

-- Inhabiting the scalar ring embedding remains a separate foundational/source
-- payment; this compiler does not manufacture it.
literalRationalRealRingEmbeddingForUnitAdjointLevel : ProofLevel
literalRationalRealRingEmbeddingForUnitAdjointLevel = conditional
