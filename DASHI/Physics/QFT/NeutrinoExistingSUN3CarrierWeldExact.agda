module DASHI.Physics.QFT.NeutrinoExistingSUN3CarrierWeldExact where

------------------------------------------------------------------------
-- ACTUAL REPOSITORY SU3 CARRIER WELD -- not another SU3 definition.
--
-- Previously present, inspected original owners:
--   DASHI.Physics.YangMills.CompactLieGroupCore.Group
--   DASHI.Physics.YangMills.SUNMatrixCarrier.CertifiedSUNMatrixTheory
--   DASHI.Physics.YangMills.SU3MatrixInstance.su3MatrixGroup
--   DASHI.Physics.YangMills.SUNMatrixLieGroup
--   DASHI.Physics.YangMills.CompactLieAnalyticPackage
--
-- THE INPUT DATA IS THE ALREADY CONSTRUCTED LEPTONIC SAME-SPACE
-- Q(zeta3) 3x3 MATRIX, NOT THE QCD COLOUR GAUGE SU3 FIELD.
--
-- Mathematical root: SU3 matrix group axioms (classical); Gotô 1949
-- DOI 10.2969/jmsj/00130270 gives a global single-commutator
-- section once group topology/semisimplicity is established.
--
-- LOCAL NEW RESULT:
-- Given one certified SAME 3x3 matrix theory on the *literal*
-- (Flavour->Flavour->Q(zeta3)) carrier, the source-written exact
-- unitary/determinant witnesses select TWO elements of the
-- original Yang-Mills SU3MatrixElement type, not a shadow group.
-- T^3=I is lifted from raw matrix equality to this group subtype.
--
-- The remaining package is explicitly UNINHABITED from present
-- sources: the 3x3 matrix theory's universal finite algebra laws,
-- and function-level equality from nine pointwise Cyclotomic3 proofs.
-- We do NOT invent those proofs or use function extensionality
-- without importing that standard theorem. This carrier weld
-- does NOT assert a measured PMNS theory or colour/flavour identity.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.YangMills.CompactLieGroupCore as Core
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.SU3MatrixInstance as SU3
import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C
import DASHI.Physics.QFT.NeutrinoThreeFlavourFiniteExact as Flavour
import DASHI.Physics.QFT.NeutrinoHornedSU3RootExact as Lepton

Lepton3Matrix : Set
Lepton3Matrix =
  Flavour.Flavour → Flavour.Flavour → C.Cyclotomic3

record ExactLeptonSUN3Weld : Set₁ where
  field
    -- The SAME literal row/column table carrier as the existing
    -- Q(zeta3) CP/leptonic SU3 source; not a new Matrix wrapper.
    matrixTheory :
      SUN.CertifiedSUNMatrixTheory 3 Lepton3Matrix C.Cyclotomic3

    rootSpecial :
      SUN.IsSpecialUnitary (SUN.operations matrixTheory)
        Lepton.selectedTS

    chargedRotationSpecial :
      SUN.IsSpecialUnitary (SUN.operations matrixTheory)
        Lepton.chargedRotationT

    -- Source-specific, exact charged rotation T³ = I at the
    -- full MATRIX equality level (not only nine pointwise cells).
    chargedRotationCube :
      SUN.multiplyM (SUN.operations matrixTheory)
        (SUN.multiplyM (SUN.operations matrixTheory)
          Lepton.chargedRotationT Lepton.chargedRotationT)
        Lepton.chargedRotationT
        ≡ SUN.identityM (SUN.operations matrixTheory)

open ExactLeptonSUN3Weld public

sameSU3Group :
  (source : ExactLeptonSUN3Weld) →
  Core.Group (SUN.SUNMatrixElement (matrixTheory source))
sameSU3Group source = SU3.su3MatrixGroup (matrixTheory source)

leptonicRootAsExistingSU3 :
  (source : ExactLeptonSUN3Weld) →
  SUN.SUNMatrixElement (matrixTheory source)
leptonicRootAsExistingSU3 source =
  SUN.sunMatrix Lepton.selectedTS (rootSpecial source)

chargedRotationAsExistingSU3 :
  (source : ExactLeptonSUN3Weld) →
  SUN.SUNMatrixElement (matrixTheory source)
chargedRotationAsExistingSU3 source =
  SUN.sunMatrix Lepton.chargedRotationT
    (chargedRotationSpecial source)

-- The *only* required cyclic input of the generic horned-Goto
-- inner group action follows as a typed Group law from the actual
-- exact matrix cube, via existing SUNMatrixCarrier proof-irrelevance.
chargedRotationHasOrderDividingThree :
  (source : ExactLeptonSUN3Weld) →
  Core.multiply (sameSU3Group source)
    (Core.multiply (sameSU3Group source)
      (chargedRotationAsExistingSU3 source)
      (chargedRotationAsExistingSU3 source))
    (chargedRotationAsExistingSU3 source)
    ≡ Core.identity (sameSU3Group source)
chargedRotationHasOrderDividingThree source =
  SUN.sunMatrixExt (chargedRotationCube source)

-- Upon merging PR #1244 and importing its group reuse adapter,
-- the exported root and rotation feed into SU3GotoInput on the
-- original SUNMatrixElement group carrier. The global Gotô section
-- remains a separately attributed mathematics authority.
-- No cross-branch phantom Agda import is attempted.
