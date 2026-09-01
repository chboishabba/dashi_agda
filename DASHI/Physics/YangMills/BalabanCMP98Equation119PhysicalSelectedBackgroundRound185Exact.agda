{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119PhysicalSelectedBackgroundRound185Exact where

------------------------------------------------------------------------
-- ROUND185 A1 BIDI: EQ. (119) REALIZATION TARGETS THE ALREADY-OWNED PHYSICAL
-- SELECTED BACKGROUND, NOT A SECOND ABSTRACT `selectedBondGroup` FIELD
--
-- Primary sources:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
-- Tadeusz Bałaban, "The Variational Problem and Background Fields in
-- Renormalization Group Method for Lattice Gauge Theories",
-- Commun. Math. Phys. 102 (1985), 605--636. DOI: 10.1007/BF01229381.
--
-- The older physical-radius instantiation already proves
--
--   Selected.selectedBondGroup ...
--     = Physical.link (Selected.selectedBackground ...).
--
-- Hence R170's equality
--
--   source.realization.bondField = Selected.selectedBondGroup ...
--
-- is not the strongest physical boundary.  On the literal side-four rational
-- carrier it is derived from the one meaningful same-object equality
--
--   source.realization.bondField
--     = Physical.link (Selected.selectedBackground ...).
--
-- This removes the independently selectable interpretation of
-- `selectedBondGroup` from the Eq. (119) producer path.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (_≤_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact as Selected
import DASHI.Physics.YangMills.BalabanSelectedBackgroundPhysicalRadiusInstantiationExact as PhysicalSelected
import DASHI.Physics.YangMills.BalabanClayGate4BackgroundFieldVariationalTheoremExact as Variational
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogPathBoundExact as Path
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanCMP98UnitaryOperatorDefectTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanCMP98MinimalContourSourceChartBudgetExact as Budget
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Equation119SelectedBackgroundBondWeldRound170Exact as R170
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushSelectedCutProducerRound178Exact as R178
import DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveCoarseBondSourceRound182Exact as R182

record PhysicalSelectedBackgroundEq119Inputs
    {CoarseField : Set}
    {group : Bond.ExactLinkGroup Q.RationalQuaternion}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier 3 4 Q.RationalQuaternion group) : Set₁ where
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
      Bond.bondField (R182.realization source step) bond
      ≡ Physical.link
          (Selected.selectedBackground
            (PhysicalSelected.bridge physical)
            (coarseAt step) (smallAt step))
          bond

    kernel : Telescope.UnitaryOperatorDefectKernel Q.RationalQuaternion

    kernelIdentityIsGroupIdentity :
      Telescope.identity kernel ≡ Bond.identity group

    kernelMultiplyIsGroupMultiply : ∀ left right →
      Telescope.multiply kernel left right
      ≡ Bond.multiply group left right

    defectInverseInvariant : ∀ value →
      Telescope.defect kernel (Bond.inverse group value)
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
    {group : Bond.ExactLinkGroup Q.RationalQuaternion}
    {source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier 3 4 Q.RationalQuaternion group}
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
    {group : Bond.ExactLinkGroup Q.RationalQuaternion}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier 3 4 Q.RationalQuaternion group) →
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

-- The abstract selectedBondGroup same-object seam is gone on this route.
-- Remaining high-alpha realization statement:
--
--   source.realization.bondField
--     = Physical.link (selectedBackground ...).
--
-- Constructing the periodic realization directly from that physical background
-- would make this equality definitional and delete the final background weld.
literalCMP98PhysicalBackgroundRealizationRound185Level : ProofLevel
literalCMP98PhysicalBackgroundRealizationRound185Level = conditional
