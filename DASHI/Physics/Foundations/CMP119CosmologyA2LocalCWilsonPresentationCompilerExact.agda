{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyA2LocalCWilsonPresentationCompilerExact where

------------------------------------------------------------------------
-- A2 SOURCE CONSTRUCTION FROM ALREADY-SELECTED LOCAL-C + WILSON DATA.
--
-- The selected Round109 stress is already proved to be the SAME Local-C stress
-- object.  The marked E2 lane already exposes an encoding
--
--   encodeStress : StressTensor -> Configuration -> R.
--
-- Therefore the selected R109 cylinder is not an independent observable
-- choice: use encodeStress on the pinned Local-C stress tensor.  Likewise, the
-- pinned published Wilson RP application proves gauge invariance and
-- positive-time admissibility for every observable on that same cylinder
-- carrier, so A2 does not need two fresh admissibility proofs.
--
-- What remains upstream is only the already-existing stress-cylinder encoding
-- authority plus the already-existing R109/Local-C provenance/completion weld.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressE2PinnedOSAlgebraExact as E2
import DASHI.Physics.Foundations.CMP119CosmologyR109WilsonAdmissibleStressCylinderExact as A2
import DASHI.Physics.YangMills.BalabanStressSameObjectProvenanceRound110Exact as R110
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119Round109ConcreteLocalCExact as Round109
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119WilsonSourceOS2Exact as WilsonSource
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as OSSystem
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as LocalC

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
    (provenance : R110.LiteralStressSameObjectProvenance Y group)
    (round109 : Round109.Round109ConcreteLocalCStressWeld Y group localC)
    (completionMatches :
      R110.markedCompletion provenance ≡ Round109.completion round109)
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

  fromLocalCEncodingAndWilsonApplication :
    A2.WilsonAdmissibleR109StressCylinderPresentation
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
  fromLocalCEncodingAndWilsonApplication = record
    { A2.WilsonAdmissibleR109StressCylinderPresentation.provenance = provenance
    ; A2.WilsonAdmissibleR109StressCylinderPresentation.round109 = round109
    ; A2.WilsonAdmissibleR109StressCylinderPresentation.completionMatches =
        completionMatches
    ; A2.WilsonAdmissibleR109StressCylinderPresentation.publishedOS =
        WilsonSource.published wilsonApplication
    ; A2.WilsonAdmissibleR109StressCylinderPresentation.stressInsertionObservable =
        selectedObservable
    ; A2.WilsonAdmissibleR109StressCylinderPresentation.stressInsertionPositiveTime =
        WilsonSource.positiveTimeMeaning wilsonApplication selectedObservable
    ; A2.WilsonAdmissibleR109StressCylinderPresentation.stressInsertionGaugeInvariant =
        WilsonSource.positiveTimeGaugeInvariant wilsonApplication selectedObservable
    }

localCStressEncodingPaysObservableConstruction : Bool
localCStressEncodingPaysObservableConstruction = true

publishedWilsonApplicationPaysAdmissibility : Bool
publishedWilsonApplicationPaysAdmissibility = true

noIndependentA2SelectedObservable : Bool
noIndependentA2SelectedObservable = true

noIndependentA2PositiveTimeProof : Bool
noIndependentA2PositiveTimeProof = true

noIndependentA2GaugeInvariantProof : Bool
noIndependentA2GaugeInvariantProof = true

remainingA2SourceDebtIsAlreadyExistingStressEncodingAuthority : Bool
remainingA2SourceDebtIsAlreadyExistingStressEncodingAuthority = true
