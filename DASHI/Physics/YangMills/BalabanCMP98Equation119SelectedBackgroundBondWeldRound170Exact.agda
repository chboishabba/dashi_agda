{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119SelectedBackgroundBondWeldRound170Exact where

------------------------------------------------------------------------
-- ROUND170 A1 BIDI: EQ. (119) POSITIVE BONDS ARE THE SELECTED BACKGROUND
--
-- Primary sources:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban, "The Variational Problem and Background Fields in
-- Renormalization Group Method for Lattice Gauge Theories",
-- Commun. Math. Phys. 102 (1985), 605--636. DOI: 10.1007/BF01229381.
--
-- Round169 reduced the whole relative-path estimate to positive-link smallness.
-- This round removes that smallness receipt when the literal Eq. (119) bond
-- field is the SAME selected variational background already owned by the
-- repository.  The source theorem gives the bond deviation bound; the bridge
-- identifies that deviation with the selected group defect; one same-object
-- equality identifies the selected group element with the actual bond stored
-- by `source.realization`.
--
-- Round172 separately proves the canonical radius-six contour has length <=24,
-- so even that geometry field is no longer accepted here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (PositiveBond; pair)
import DASHI.Physics.YangMills.BalabanClayGate4BackgroundFieldVariationalTheoremExact as Variational
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Scale
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogPathBoundExact as Path
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact as Selected
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveLinkDefectRound168Exact as R168
import DASHI.Physics.YangMills.BalabanCMP98CanonicalContourLength24Round172Exact as R172
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanCMP98UnitaryOperatorDefectTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanCMP98MinimalContourSourceChartBudgetExact as Budget

record SelectedBackgroundBondWeld
    {C n Value group CoarseField FineField Lie}
    (source : R158.CanonicalL13Equation119Source C n Value group) : Set₁ where
  field
    bridge : Selected.SelectedBackgroundVariationalChartBridge
      CoarseField FineField (PositiveBond (suc n)) Lie Value ℚ

    coarseAt : Nat → CoarseField
    smallAt : ∀ step →
      Variational.CoarseSmallField
        (Selected.variational bridge) (coarseAt step)

    realizationBondIsSelected : ∀ step bond →
      Bond.bondField
        (R158.CanonicalL13Equation119Source.realization source step) bond
      ≡ Selected.selectedBondGroup bridge
          (coarseAt step) (smallAt step) bond

    kernel : Telescope.UnitaryOperatorDefectKernel Value

    kernelIdentityIsGroupIdentity :
      Telescope.identity kernel ≡ Bond.identity group

    kernelMultiplyIsGroupMultiply : ∀ left right →
      Telescope.multiply kernel left right ≡ Bond.multiply group left right

    defectInverseInvariant : ∀ value →
      Telescope.defect kernel (Bond.inverse group value)
      ≡ Telescope.defect kernel value

    kernelDefectIsSelectedDefect : ∀ value →
      Telescope.defect kernel value
      ≡ Path.defect (Selected.defectAlgebra bridge) value

    chartOrderIsRationalOrder :
      Scale.LessEqual (Path.scale (Selected.defectAlgebra bridge))
      ≡ _≤_

    publishedUpperBelowPerLinkMajorant :
      Selected.sourceFineBondUpper (Selected.variational bridge)
      ≤ Budget.perLinkDefectMajorant

open SelectedBackgroundBondWeld public

selectedGroupDefectBelowPublishedUpper :
  ∀ {C n Value group CoarseField FineField Lie}
    {source : R158.CanonicalL13Equation119Source C n Value group}
    (weld : SelectedBackgroundBondWeld
      {CoarseField = CoarseField} {FineField = FineField} {Lie = Lie} source)
    step bond →
  Path.defect (Selected.defectAlgebra (bridge weld))
    (Selected.selectedBondGroup (bridge weld)
      (coarseAt weld step) (smallAt weld step) bond)
  ≤ Selected.sourceFineBondUpper (Selected.variational (bridge weld))
selectedGroupDefectBelowPublishedUpper weld step bond =
  let
    b = bridge weld
    theorem = Selected.variational b
    coarse = coarseAt weld step
    small = smallAt weld step
    upper = Selected.sourceFineBondUpper theorem
    deviation =
      Variational.bondDeviation theorem
        (Variational.bondValue theorem
          (Variational.background theorem coarse small) bond)
        (Variational.identityBondValue theorem)

    sourceBound :
      Variational.LessEqual theorem deviation upper
    sourceBound = Variational.fineBondSmallness theorem coarse small bond

    selectedOrderBound :
      Scale.LessEqual (Path.scale (Selected.defectAlgebra b)) deviation upper
    selectedOrderBound =
      subst
        (λ relation → relation deviation upper)
        (Selected.variationalOrderIsChartOrder b)
        sourceBound

    selectedOrderAsRational : deviation ≤ upper
    selectedOrderAsRational =
      subst
        (λ relation → relation deviation upper)
        (chartOrderIsRationalOrder weld)
        selectedOrderBound
  in
  subst
    (λ lower → lower ≤ upper)
    (sym (Selected.defectMatchesPublishedBondDeviation b coarse small bond))
    selectedOrderAsRational

selectedKernelDefectBelowPerLinkMajorant :
  ∀ {C n Value group CoarseField FineField Lie}
    {source : R158.CanonicalL13Equation119Source C n Value group}
    (weld : SelectedBackgroundBondWeld
      {CoarseField = CoarseField} {FineField = FineField} {Lie = Lie} source)
    step bond →
  Telescope.defect (kernel weld)
    (Bond.bondField
      (R158.CanonicalL13Equation119Source.realization source step) bond)
  ≤ Budget.perLinkDefectMajorant
selectedKernelDefectBelowPerLinkMajorant weld step bond =
  let
    selected = Selected.selectedBondGroup (bridge weld)
      (coarseAt weld step) (smallAt weld step) bond
    selectedBound = selectedGroupDefectBelowPublishedUpper weld step bond
    selectedKernelBound :
      Telescope.defect (kernel weld) selected
      ≤ Selected.sourceFineBondUpper (Selected.variational (bridge weld))
    selectedKernelBound =
      subst
        (λ lower → lower
          ≤ Selected.sourceFineBondUpper (Selected.variational (bridge weld)))
        (sym (kernelDefectIsSelectedDefect weld selected))
        selectedBound
    finalSelected =
      ℚP.≤-trans selectedKernelBound
        (publishedUpperBelowPerLinkMajorant weld)
  in
  subst
    (λ value → Telescope.defect (kernel weld) value
      ≤ Budget.perLinkDefectMajorant)
    (sym (realizationBondIsSelected weld step bond))
    finalSelected

asPositiveLinkDefectInputs :
  ∀ {C n Value group CoarseField FineField Lie}
    (source : R158.CanonicalL13Equation119Source C n Value group) →
  SelectedBackgroundBondWeld
    {CoarseField = CoarseField} {FineField = FineField} {Lie = Lie} source →
  R168.PositiveLinkDefectInputs source
asPositiveLinkDefectInputs source weld = record
  { R168.PositiveLinkDefectInputs.kernel = kernel weld
  ; R168.PositiveLinkDefectInputs.kernelIdentityIsGroupIdentity =
      kernelIdentityIsGroupIdentity weld
  ; R168.PositiveLinkDefectInputs.kernelMultiplyIsGroupMultiply =
      kernelMultiplyIsGroupMultiply weld
  ; R168.PositiveLinkDefectInputs.defectInverseInvariant =
      defectInverseInvariant weld
  ; R168.PositiveLinkDefectInputs.positiveBondDefectSmall =
      λ step site axis →
        selectedKernelDefectBelowPerLinkMajorant weld step (pair site axis)
  ; R168.PositiveLinkDefectInputs.canonicalContourLengthAtMost24 =
      R172.canonicalContourLengthAtMost24
  }

cmp98Equation119SelectedBackgroundBondWeldRound170Level : ProofLevel
cmp98Equation119SelectedBackgroundBondWeldRound170Level = machineChecked

literalCMP98SelectedVariationalBridgeInstantiationRound170Level : ProofLevel
literalCMP98SelectedVariationalBridgeInstantiationRound170Level = conditional
