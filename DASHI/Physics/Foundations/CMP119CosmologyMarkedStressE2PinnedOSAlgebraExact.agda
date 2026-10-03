{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyMarkedStressE2PinnedOSAlgebraExact where

------------------------------------------------------------------------
-- E2 ON THE ACTUAL PINNED CMP119 OS CYLINDER ALGEBRA.
--
-- The generic marked-E2 compiler is already enough once the selected stress
-- mark is an admissible reflected positive-time cylinder observable.  This
-- owner removes the remaining arbitrary OS algebra choice: the target algebra
-- is exactly OSSystem.observableAlgebra osInputs on the same CMP119 family.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressE2CylinderEmbeddingExact as E2
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as LocalC
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as OSSystem

record PinnedLocalCStressCylinderEmbedding
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
    : Set₁ where
  field
    encodeStress :
      Top.StressTensor C → Configuration → ℝ

    PositiveTimeSupported :
      (Configuration → ℝ) → Set

    GaugeInvariantObservable :
      (Configuration → ℝ) → Set

    selectedStressPositiveTime :
      PositiveTimeSupported
        (encodeStress (LocalC.stressTensor localC))

    selectedStressGaugeInvariant :
      GaugeInvariantObservable
        (encodeStress (LocalC.stressTensor localC))

    reflectStressMark :
      Top.StressTensor C → Top.StressTensor C

    allStressPositiveTime :
      ∀ stress → PositiveTimeSupported (encodeStress stress)

    allStressGaugeInvariant :
      ∀ stress → GaugeInvariantObservable (encodeStress stress)

    encodeCommutesWithReflection :
      ∀ stress →
      encodeStress (reflectStressMark stress)
      ≡
      DASHI.Physics.YangMills.YangMillsCylinderLimitOSReflectionPositiveExact.reflectObservable
        (OSSystem.observableAlgebra osInputs)
        (encodeStress stress)

open PinnedLocalCStressCylinderEmbedding public

asMarkedStressCylinderEmbedding :
  ∀ {C S Y group
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division osS osInputs reconstruction
      localC} →
  PinnedLocalCStressCylinderEmbedding
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
    localC →
  E2.MarkedStressCylinderEmbedding
    (Configuration → ℝ)
    (Top.StressTensor C)
    (OSSystem.observableAlgebra osInputs)
asMarkedStressCylinderEmbedding embedding = record
  { E2.MarkedStressCylinderEmbedding.encodeStress = encodeStress embedding
  ; E2.MarkedStressCylinderEmbedding.PositiveTimeSupported =
      PositiveTimeSupported embedding
  ; E2.MarkedStressCylinderEmbedding.GaugeInvariantObservable =
      GaugeInvariantObservable embedding
  ; E2.MarkedStressCylinderEmbedding.stressPositiveTime =
      allStressPositiveTime embedding
  ; E2.MarkedStressCylinderEmbedding.stressGaugeInvariant =
      allStressGaugeInvariant embedding
  ; E2.MarkedStressCylinderEmbedding.reflectStressMark =
      reflectStressMark embedding
  ; E2.MarkedStressCylinderEmbedding.encodeCommutesWithReflection =
      encodeCommutesWithReflection embedding
  }

selectedStressE2SupportAlreadyExplicit :
  ∀ {C S Y group
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division osS osInputs reconstruction
      localC}
    (embedding :
      PinnedLocalCStressCylinderEmbedding
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
        localC) →
  PositiveTimeSupported embedding
    (encodeStress embedding (LocalC.stressTensor localC))
selectedStressE2SupportAlreadyExplicit = selectedStressPositiveTime

markedE2AlgebraChoiceNoLongerFree : Bool
markedE2AlgebraChoiceNoLongerFree = true

markedE2PhysicalLeafIsStressCylinderEncodingAndAdmissibility : Bool
markedE2PhysicalLeafIsStressCylinderEncodingAndAdmissibility = true
