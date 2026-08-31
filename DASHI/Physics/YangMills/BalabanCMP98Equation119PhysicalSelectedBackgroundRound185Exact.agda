{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119PhysicalSelectedBackgroundRound185Exact where

------------------------------------------------------------------------
-- ROUND185 A1 BIDI: THE SELECTED-BACKGROUND WELD TARGET IS THE ALREADY-OWNED
-- PHYSICAL LINK, NOT A SECOND ABSTRACT GROUP FIELD
--
-- Primary sources:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
-- Tadeusz Bałaban, "The Variational Problem and Background Fields in
-- Renormalization Group Method for Lattice Gauge Theories",
-- Commun. Math. Phys. 102 (1985), 605--636. DOI: 10.1007/BF01229381.
--
-- R170 still asks for
--
--   realization bond = Selected.selectedBondGroup ...
--
-- while the older physical-radius instantiation already proves
--
--   Selected.selectedBondGroup ... = Physical.link(selectedBackground ...) .
--
-- BIDI therefore moves the same-object seam one layer upstream: on the
-- rational side-four physical carrier the only realization equality we retain
-- is the meaningful one
--
--   realization bond = Physical.link(selectedBackground ...).
--
-- The R170 equality is derived by transitivity.  Callers can no longer choose
-- an independent `selectedBondGroup` interpretation for Eq. (119).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact as Selected
import DASHI.Physics.YangMills.BalabanSelectedBackgroundPhysicalRadiusInstantiationExact as PhysicalSelected
import DASHI.Physics.YangMills.BalabanClayGate4BackgroundFieldVariationalTheoremExact as Variational
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Scale
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogPathBoundExact as Path
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanCMP98UnitaryOperatorDefectTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanCMP98MinimalContourSourceChartBudgetExact as Budget
import DASHI.Physics.YangMills.BalabanCMP98Equation119SelectedBackgroundBondWeldRound170Exact as R170
import DASHI.Physics.YangMills.BalabanCMP98Equation119SelectedExistingCutRound175Exact as R175
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushCalculusReuseRound177Exact as R177
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushSelectedCutProducerRound178Exact as R178
import DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveCoarseBondSourceRound182Exact as R182
import DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveBondSelectedCutFederbushRound184Exact as R184

record PhysicalSelectedBackgroundEq119Inputs
    {CoarseField : Set}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier 3 4 Q.RationalQuaternion
      (R182.R158.CanonicalL13Equation119Source.group
        (R182.asCanonicalL13Equation119Source source))) : Set₁ where
  field
    physical :
      PhysicalSelected.SelectedPhysicalBackgroundInstantiation
        CoarseField Lie.SU2LieAlgebra

    coarseAt : Nat → CoarseField
    smallAt : ∀ step →
      Variational.CoarseSmallField
        (Selected.variational (PhysicalSelected.bridge physical))
        (coarseAt step)

    realizationBondIsPhysicalLink : ∀ step bond →
      Bond.bondField
        (R182.realization source step) bond
      ≡ Physical.link
          (Selected.selectedBackground
            (PhysicalSelected.bridge physical)
            (coarseAt step) (smallAt step))
          bond

    kernel : Telescope.UnitaryOperatorDefectKernel Q.RationalQuaternion

    kernelIdentityIsGroupIdentity :
      Telescope.identity kernel
      ≡ Bond.identity
          (R182.R158.CanonicalL13Equation119Source.group
            (R182.asCanonicalL13Equation119Source source))

    kernelMultiplyIsGroupMultiply : ∀ left right →
      Telescope.multiply kernel left right
      ≡ Bond.multiply
          (R182.R158.CanonicalL13Equation119Source.group
            (R182.asCanonicalL13Equation119Source source))
          left right

    defectInverseInvariant : ∀ value →
      Telescope.defect kernel
        (Bond.inverse
          (R182.R158.CanonicalL13Equation119Source.group
            (R182.asCanonicalL13Equation119Source source)) value)
      ≡ Telescope.defect kernel value

    kernelDefectIsSelectedDefect : ∀ value →
      Telescope.defect kernel value
      ≡ Path.defect
          (Selected.defectAlgebra (PhysicalSelected.bridge physical)) value

    publishedUpperBelowPerLinkMajorant :
      Selected.sourceFineBondUpper
        (Selected.variational (PhysicalSelected.bridge physical))
      ≤ Budget.perLinkDefectMajorant

open PhysicalSelectedBackgroundEq119Inputs public

realizationBondIsSelectedGroup :
  ∀ {CoarseField}
    {source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier 3 4 Q.RationalQuaternion
      (R182.R158.CanonicalL13Equation119Source.group
        (R182.asCanonicalL13Equation119Source source))}
    (inputs : PhysicalSelectedBackgroundEq119Inputs
      {CoarseField = CoarseField} source)
    step bond →
  Bond.bondField (R182.realization source step) bond
  ≡ Selected.selectedBondGroup
      (PhysicalSelected.bridge (physical inputs))
      (coarseAt inputs step) (smallAt inputs step) bond
realizationBondIsSelectedGroup inputs step bond =
  trans
    (realizationBondIsPhysicalLink inputs step bond)
    (sym
      (PhysicalSelected.selectedBondGroupIsPhysicalLink
        (physical inputs)
        (coarseAt inputs step) (smallAt inputs step) bond))

asRound170SelectedBackgroundWeld :
  ∀ {CoarseField}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier 3 4 Q.RationalQuaternion
      (R182.R158.CanonicalL13Equation119Source.group
        (R182.asCanonicalL13Equation119Source source))) →
  PhysicalSelectedBackgroundEq119Inputs
    {CoarseField = CoarseField} source →
  R170.SelectedBackgroundBondWeld
    {CoarseField = CoarseField}
    {FineField = Physical.RationalSU2Background4}
    {Lie = Lie.SU2LieAlgebra}
    (R182.asCanonicalL13Equation119Source source)
asRound170SelectedBackgroundWeld source inputs = record
  { R170.SelectedBackgroundBondWeld.bridge =
      PhysicalSelected.bridge (physical inputs)
  ; R170.SelectedBackgroundBondWeld.coarseAt = coarseAt inputs
  ; R170.SelectedBackgroundBondWeld.smallAt = smallAt inputs
  ; R170.SelectedBackgroundBondWeld.realizationBondIsSelected =
      realizationBondIsSelectedGroup inputs
  ; R170.SelectedBackgroundBondWeld.kernel = kernel inputs
  ; R170.SelectedBackgroundBondWeld.kernelIdentityIsGroupIdentity =
      kernelIdentityIsGroupIdentity inputs
  ; R170.SelectedBackgroundBondWeld.kernelMultiplyIsGroupMultiply =
      kernelMultiplyIsGroupMultiply inputs
  ; R170.SelectedBackgroundBondWeld.defectInverseInvariant =
      defectInverseInvariant inputs
  ; R170.SelectedBackgroundBondWeld.kernelDefectIsSelectedDefect =
      kernelDefectIsSelectedDefect inputs
  ; R170.SelectedBackgroundBondWeld.chartOrderIsRationalOrder =
      PhysicalSelected.chartOrderIsRationalOrder (physical inputs)
  ; R170.SelectedBackgroundBondWeld.publishedUpperBelowPerLinkMajorant =
      publishedUpperBelowPerLinkMajorant inputs
  }

cmp98Equation119PhysicalSelectedBackgroundRound185Level : ProofLevel
cmp98Equation119PhysicalSelectedBackgroundRound185Level = machineChecked

-- The abstract selectedBondGroup equality is gone on this route.  The remaining
-- physical realization seam is now exactly the intended one:
--
--   source.realization.bondField = Physical.link(selectedBackground).
--
-- Next BIDI target: construct `source.realization` directly from that physical
-- background (and the repository exact SU(2) group/gauge realization), making
-- even this equality definitional.
literalCMP98PhysicalBackgroundRealizationRound185Level : ProofLevel
literalCMP98PhysicalBackgroundRealizationRound185Level = conditional
