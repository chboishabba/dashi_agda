{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyLocalCSelectedCylinderDirectExact where

------------------------------------------------------------------------
-- DIRECT LOCAL-C -> SELECTED CYLINDER MAX-CUT.
--
-- The marked OS E2/E4 consumer only needs the one selected Local-C stress
-- represented as a positive-time, gauge-invariant cylinder observable.
-- It does NOT consume the abstract Round109 insertion-pair value.
--
-- Once the existing physical stress-cylinder encoding
--
--   encodeStress : StressTensor -> Configuration -> R
--
-- and the already-pinned Wilson RP application are present, construct the
-- selected cylinder directly.  The same-object meaning relation is definitionally
-- tied to `encodeStress`; no Round109 pair -> observable semantics is needed.
--
-- Round109 remains connected to the same physical stress at the COMPLETED
-- endpoint through the independent Round109/Local-C same-object weld.  Requiring
-- a second finite-presentation identity between its opaque insertion-pair
-- carrier and this cylinder observable was therefore unnecessary for E2/E4.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressE2PinnedOSAlgebraExact as E2
import DASHI.Physics.Foundations.CMP119CosmologySelectedLocalCStressCylinderExact as Selected
import DASHI.Physics.YangMills.BalabanClayOSWilsonReflectionPositivityExact as WilsonOS
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as LocalC
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as OSSystem
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119WilsonSourceOS2Exact as WilsonSource

module _
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C)
    {G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient Hilbert Vector Hamiltonian Algebra
     Scale Volume Root ContinuumFamily Core
     sequenceLimit limitLaws quotient division osS osInputs reconstruction}
    (localC :
      LocalC.PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor C)
        Hilbert Vector Hamiltonian Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = osS}
        osInputs reconstruction group)
    (stressEncoding :
      E2.PinnedLocalCStressCylinderEmbedding
        {C = C} {S = S} Y group
        {G = G} {X = X} {Configuration = Configuration}
        {Position = Position} {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
        {Hilbert = Hilbert} {Vector = Vector}
        {Hamiltonian = Hamiltonian} {Algebra = Algebra}
        {Scale = Scale} {Volume = Volume} {Root = Root}
        {ContinuumFamily = ContinuumFamily} {Core = Core}
        {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
        {quotient = quotient} {division = division}
        {osS = osS} {osInputs = osInputs} {reconstruction = reconstruction}
        localC)
    (wilsonApplication :
      WilsonSource.LiteralCMP119WilsonRPApplication
        Configuration
        (OSSystem.family osInputs group)
        (OSSystem.observableAlgebra osInputs))
  where

  selectedObservable : Configuration → ℝ
  selectedObservable =
    E2.encodeStress stressEncoding (LocalC.stressTensor localC)

  directSelectedLocalCStressCylinder :
    Selected.SelectedLocalCStressCylinder
      {C = C} {S = S} Y group
      {G = G} {X = X} {Configuration = Configuration}
      {Position = Position} {CurvaturePolynomial = CurvaturePolynomial}
      {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
      {Hilbert = Hilbert} {Vector = Vector}
      {Hamiltonian = Hamiltonian} {Algebra = Algebra}
      {Scale = Scale} {Volume = Volume} {Root = Root}
      {ContinuumFamily = ContinuumFamily} {Core = Core}
      {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
      {quotient = quotient} {division = division}
      {osS = osS} {osInputs = osInputs} {reconstruction = reconstruction}
      localC
  directSelectedLocalCStressCylinder = record
    { Selected.SelectedLocalCStressCylinder.selectedObservable =
        selectedObservable
    ; Selected.SelectedLocalCStressCylinder.PositiveTimeSupported =
        WilsonOS.PositiveTimeObservable (WilsonSource.published wilsonApplication)
    ; Selected.SelectedLocalCStressCylinder.GaugeInvariantObservable =
        WilsonOS.GaugeInvariant (WilsonSource.published wilsonApplication)
    ; Selected.SelectedLocalCStressCylinder.selectedPositiveTime =
        WilsonSource.positiveTimeMeaning wilsonApplication selectedObservable
    ; Selected.SelectedLocalCStressCylinder.selectedGaugeInvariant =
        WilsonSource.positiveTimeGaugeInvariant wilsonApplication selectedObservable
    ; Selected.SelectedLocalCStressCylinder.SelectedStressObservableMeaning =
        λ stress observable →
          (stress ≡ LocalC.stressTensor localC)
          × (observable ≡ E2.encodeStress stressEncoding stress)
    ; Selected.SelectedLocalCStressCylinder.selectedObservableMeansLocalCStress =
        refl , refl
    }

round109PairSemanticsNotNeededForMarkedOS : Bool
round109PairSemanticsNotNeededForMarkedOS = true

selectedCylinderComesFromExistingLocalCEncoding : Bool
selectedCylinderComesFromExistingLocalCEncoding = true

round109PairToCylinderSameObjectLeafRetired : Bool
round109PairToCylinderSameObjectLeafRetired = true
