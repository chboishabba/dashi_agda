module DASHI.Physics.YangMills.BalabanP33IdentityCurvatureLocalExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks",
-- Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Identify every local cell of the side-four identity-background Wilson
-- Hessian with the exact squared forward-difference curl already proved in the
-- repository.  The local statement is then lifted through the literal finite
-- plaquette enumeration, so the reference curvature energy is not represented
-- by an unnamed form or a global receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational using (ℚ)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (Product; pair; cartesian)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (PhysicalBlockL; physicalBlockSites)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational; sumRationalCong)
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact using
  (sumCartesian)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using
  (side4)
open import DASHI.Physics.YangMills.BalabanPath4PlaquetteOrientationExact using
  (PositivePlaquettePlane4; positivePlaquettePlanes4)
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact using
  (PhysicalSU2Tangent4)
import DASHI.Physics.YangMills.BalabanPath4SU2LiteralPlaquetteLiftExact as Wilson

IdentityCurvatureCell4 : Set
IdentityCurvatureCell4 =
  Product PositivePlaquettePlane4 (PhysicalBlockL side4)

identityCurvatureCells4 : List IdentityCurvatureCell4
identityCurvatureCells4 =
  cartesian positivePlaquettePlanes4 (physicalBlockSites side4)

identityCurvatureCellHessian :
  PhysicalSU2Tangent4 → IdentityCurvatureCell4 → ℚ
identityCurvatureCellHessian tangent (pair plane site) =
  Wilson.literalPlaquetteWilsonSecondVariation tangent plane site

identityCurvatureCellCharge :
  PhysicalSU2Tangent4 → IdentityCurvatureCell4 → ℚ
identityCurvatureCellCharge tangent (pair plane site) =
  Wilson.literalPlaquetteCurlNormSq tangent plane site

identityCurvatureCellExact : ∀ tangent cell →
  identityCurvatureCellHessian tangent cell
  ≡ identityCurvatureCellCharge tangent cell
identityCurvatureCellExact tangent (pair plane site) =
  Wilson.literalPlaquetteWilsonSecondVariationExact tangent plane site

identityCurvatureHessianCellFold : PhysicalSU2Tangent4 → ℚ
identityCurvatureHessianCellFold tangent =
  sumRational identityCurvatureCells4
    (identityCurvatureCellHessian tangent)

identityCurvatureChargeCellFold : PhysicalSU2Tangent4 → ℚ
identityCurvatureChargeCellFold tangent =
  sumRational identityCurvatureCells4
    (identityCurvatureCellCharge tangent)

identityCurvatureHessianCellFoldExact : ∀ tangent →
  identityCurvatureHessianCellFold tangent
  ≡ Wilson.literalWilsonHessianPositivePlaneFold tangent
identityCurvatureHessianCellFoldExact tangent =
  sumCartesian
    positivePlaquettePlanes4
    (physicalBlockSites side4)
    (identityCurvatureCellHessian tangent)

identityCurvatureChargeCellFoldExact : ∀ tangent →
  identityCurvatureChargeCellFold tangent
  ≡ Wilson.literalDiscreteCurlEnergy tangent
identityCurvatureChargeCellFoldExact tangent =
  sumCartesian
    positivePlaquettePlanes4
    (physicalBlockSites side4)
    (identityCurvatureCellCharge tangent)

identityCurvatureCellFoldEquality : ∀ tangent →
  identityCurvatureHessianCellFold tangent
  ≡ identityCurvatureChargeCellFold tangent
identityCurvatureCellFoldEquality tangent =
  sumRationalCong
    identityCurvatureCells4
    (identityCurvatureCellHessian tangent)
    (identityCurvatureCellCharge tangent)
    (identityCurvatureCellExact tangent)

identityCurvatureMatchesLiteralWilsonAndCurl : ∀ tangent →
  Wilson.literalWilsonHessianPositivePlaneFold tangent
  ≡ Wilson.literalDiscreteCurlEnergy tangent
identityCurvatureMatchesLiteralWilsonAndCurl tangent =
  trans
    (sym (identityCurvatureHessianCellFoldExact tangent))
    (trans
      (identityCurvatureCellFoldEquality tangent)
      (identityCurvatureChargeCellFoldExact tangent))

identityCurvatureLiteralCellLevel : ProofLevel
identityCurvatureLiteralCellLevel = machineChecked

identityCurvatureLocalWilsonJetLevel : ProofLevel
identityCurvatureLocalWilsonJetLevel = machineChecked

identityCurvatureGlobalFoldLevel : ProofLevel
identityCurvatureGlobalFoldLevel = machineChecked
