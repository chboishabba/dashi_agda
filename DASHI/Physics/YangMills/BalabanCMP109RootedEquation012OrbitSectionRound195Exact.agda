{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109RootedEquation012OrbitSectionRound195Exact where

------------------------------------------------------------------------
-- ROUND195 BIDI: THE ROOTED GAUGE SECTION PRESERVES THE LITERAL CMP109
-- EQUATION-(0.12) MAP ON A COARSE-ANCHORED ONE-BLOCK FIBRE.
--
-- Existing owners already prove:
--
--   * every finite gauge field has a canonical based rooted representative;
--   * the literal printed equation-(0.12) map is fixed by any gauge whose
--     source/target coarse endpoint values are the group identity.
--
-- This file composes those results on the SAME gauge function.  The only
-- same-object inputs are that the equation-(0.12) gauge action is the physical
-- bond gauge action used by the rooted section, that its two coarse endpoint
-- gauges are evaluation at the rooted coarse site, and that the group-average
-- identity is the physical gauge-group unit.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Transport
import DASHI.Physics.YangMills.BalabanGaugeTransformationCovariance as Covariance
import DASHI.Physics.YangMills.BalabanBasedPathGaugeSectionExact as Rooted
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PrintedPathFormulaExact as Printed
import DASHI.Physics.YangMills.BalabanClayGate4CMP109GroupAverageAxiomsExact as Average
import DASHI.Physics.YangMills.BalabanCMP109Equation012CoarseAnchoredGaugeExact as Eq012

record RootedEquation012SameObjectInputs
    {CoarseBond FineSite Lie Scalar : Set}
    {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N)
    (paths : Rooted.RootedPathSystem base)
    (averageAxioms : Average.CMP109GroupAverageAxioms
      (Transport.Carrier group) Lie Scalar)
    (printed : Printed.PrintedCMP109Equation012Data
      (Covariance.DirectedGaugeField4 N group)
      CoarseBond FineSite (Transport.Carrier group) Lie Scalar)
    (gaugeData : Eq012.Equation012GaugeActionData
      (Covariance.DirectedGaugeField4 N group)
      (Covariance.GaugeFunction4 N group)
      CoarseBond FineSite (Transport.Carrier group) Lie Scalar
      averageAxioms printed) : Set₁ where
  field
    gaugeActionIsPhysical : ∀ gauge field →
      Eq012.gaugeAction gaugeData gauge field
      ≡ Covariance.gaugeTransformBond group gauge field

    sourceGaugeIsRootEvaluation : ∀ gauge coarse →
      Eq012.sourceGauge gaugeData gauge coarse ≡ gauge base

    targetGaugeIsRootEvaluation : ∀ gauge coarse →
      Eq012.targetGauge gaugeData gauge coarse ≡ gauge base

    averageIdentityIsPhysicalUnit :
      Average.identity averageAxioms ≡ Transport.unit group

open RootedEquation012SameObjectInputs public

rootedEquation012SourceAnchored :
  ∀ {CoarseBond FineSite Lie Scalar N}
    {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base}
    {averageAxioms : Average.CMP109GroupAverageAxioms
      (Transport.Carrier group) Lie Scalar}
    {printed : Printed.PrintedCMP109Equation012Data
      (Covariance.DirectedGaugeField4 N group)
      CoarseBond FineSite (Transport.Carrier group) Lie Scalar}
    {gaugeData : Eq012.Equation012GaugeActionData
      (Covariance.DirectedGaugeField4 N group)
      (Covariance.GaugeFunction4 N group)
      CoarseBond FineSite (Transport.Carrier group) Lie Scalar
      averageAxioms printed}
    (inputs : RootedEquation012SameObjectInputs
      group base paths averageAxioms printed gaugeData)
    field coarse →
  Eq012.sourceGauge gaugeData
    (Rooted.rootedGaugeFunction group paths field) coarse
  ≡ Average.identity averageAxioms
rootedEquation012SourceAnchored
    {group = group} {paths = paths} inputs field coarse =
  trans
    (sourceGaugeIsRootEvaluation inputs
      (Rooted.rootedGaugeFunction group paths field) coarse)
    (trans
      (Rooted.rootedGaugeFunctionBased group paths field)
      (sym (averageIdentityIsPhysicalUnit inputs)))

rootedEquation012TargetAnchored :
  ∀ {CoarseBond FineSite Lie Scalar N}
    {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base}
    {averageAxioms : Average.CMP109GroupAverageAxioms
      (Transport.Carrier group) Lie Scalar}
    {printed : Printed.PrintedCMP109Equation012Data
      (Covariance.DirectedGaugeField4 N group)
      CoarseBond FineSite (Transport.Carrier group) Lie Scalar}
    {gaugeData : Eq012.Equation012GaugeActionData
      (Covariance.DirectedGaugeField4 N group)
      (Covariance.GaugeFunction4 N group)
      CoarseBond FineSite (Transport.Carrier group) Lie Scalar
      averageAxioms printed}
    (inputs : RootedEquation012SameObjectInputs
      group base paths averageAxioms printed gaugeData)
    field coarse →
  Eq012.targetGauge gaugeData
    (Rooted.rootedGaugeFunction group paths field) coarse
  ≡ Average.identity averageAxioms
rootedEquation012TargetAnchored
    {group = group} {paths = paths} inputs field coarse =
  trans
    (targetGaugeIsRootEvaluation inputs
      (Rooted.rootedGaugeFunction group paths field) coarse)
    (trans
      (Rooted.rootedGaugeFunctionBased group paths field)
      (sym (averageIdentityIsPhysicalUnit inputs)))

rootedEquation012MapPreserved :
  ∀ {CoarseBond FineSite Lie Scalar N}
    {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base}
    {averageAxioms : Average.CMP109GroupAverageAxioms
      (Transport.Carrier group) Lie Scalar}
    (laws : Eq012.CMP109GroupLaws averageAxioms)
    {printed : Printed.PrintedCMP109Equation012Data
      (Covariance.DirectedGaugeField4 N group)
      CoarseBond FineSite (Transport.Carrier group) Lie Scalar}
    {gaugeData : Eq012.Equation012GaugeActionData
      (Covariance.DirectedGaugeField4 N group)
      (Covariance.GaugeFunction4 N group)
      CoarseBond FineSite (Transport.Carrier group) Lie Scalar
      averageAxioms printed}
    (inputs : RootedEquation012SameObjectInputs
      group base paths averageAxioms printed gaugeData)
    field coarse →
  Printed.printedEquation012Map printed
    (Rooted.rootedGaugeRepresentative group paths field) coarse
  ≡ Printed.printedEquation012Map printed field coarse
rootedEquation012MapPreserved
    {group = group} {paths = paths} {printed = printed}
    {gaugeData = gaugeData} laws inputs field coarse =
  let
    gauge = Rooted.rootedGaugeFunction group paths field

    underGaugeData :
      Printed.printedEquation012Map printed
        (Eq012.gaugeAction gaugeData gauge field) coarse
      ≡ Printed.printedEquation012Map printed field coarse
    underGaugeData =
      Eq012.equation012MapFixedByCoarseAnchoredGauge
        laws gaugeData gauge field coarse
        (rootedEquation012SourceAnchored inputs field coarse)
        (rootedEquation012TargetAnchored inputs field coarse)

    rootedIsGaugeData :
      Rooted.rootedGaugeRepresentative group paths field
      ≡ Eq012.gaugeAction gaugeData gauge field
    rootedIsGaugeData =
      sym (gaugeActionIsPhysical inputs gauge field)
  in
  trans
    (cong
      (λ selectedField →
        Printed.printedEquation012Map printed selectedField coarse)
      rootedIsGaugeData)
    underGaugeData

cmp109RootedEquation012OrbitSectionRound195Level : ProofLevel
cmp109RootedEquation012OrbitSectionRound195Level = machineChecked

cmp109RootedEquation012MapPreservationRound195Level : ProofLevel
cmp109RootedEquation012MapPreservationRound195Level = machineChecked

literalCMP109Equation012GaugeActionPhysicalRound195Level : ProofLevel
literalCMP109Equation012GaugeActionPhysicalRound195Level = conditional

literalCMP109Equation012CoarseEndpointsAreRootRound195Level : ProofLevel
literalCMP109Equation012CoarseEndpointsAreRootRound195Level = conditional

literalCMP109Equation012IdentityIsPhysicalUnitRound195Level : ProofLevel
literalCMP109Equation012IdentityIsPhysicalUnitRound195Level = conditional
