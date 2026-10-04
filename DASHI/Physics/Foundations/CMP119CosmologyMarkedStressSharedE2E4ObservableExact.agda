{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyMarkedStressSharedE2E4ObservableExact where

------------------------------------------------------------------------
-- ONE SELECTED LOCAL-C STRESS OBSERVABLE PAYS BOTH MARKED E2 AND MARKED E4.
--
-- E2 already asks for an encoding
--
--   encodeStress : StressTensor -> Configuration -> R
--
-- into the ACTUAL pinned CMP119 cylinder algebra, together with positive-time,
-- gauge-invariance and reflection compatibility.
--
-- Round281's E4 route only needs the selected stress to be the literal
-- Observable whose sourceDirectionOf is differentiated.  Specialize its
-- Observable carrier to the SAME cylinder carrier `Configuration -> R` and use
-- the E2 encoding definitionally.  Then no second Local-C stress-observable map
-- is a physical premise, and the existing Round279/281 clustering theorem
-- supplies the decay.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressE2PinnedOSAlgebraExact as E2
import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressE4Round281Exact as E4
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as LocalC
import DASHI.Physics.YangMills.BalabanCMP116119NormalizedExpectationDerivativeRound281Exact as R281
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant

record SharedPinnedStressObservable
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
    {Scalar SourceDirection : Set}
    {algebra : Cumulant.TwoSourceMomentAlgebra (Configuration → ℝ) Scalar}
    {calculus : Cumulant.NormalizedLogSourceCalculus algebra}
    {published : R281.CMP116119PublishedTwoSourceLocalization Scale Volume Root}
    {meaning : Cumulant.LiteralTwoSourceInsertionMeaning calculus SourceDirection}
    (round281 : R281.LiteralTwoSourceNormalizedExpectationWeld published meaning)
    : Set₁ where
  field
    cylinderEmbedding :
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
        localC

open SharedPinnedStressObservable public

asRound281StressSelection :
  ∀ {C S Y group
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division osS osInputs reconstruction
      localC Scalar SourceDirection algebra calculus published meaning round281} →
  SharedPinnedStressObservable
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
    {Scalar = Scalar} {SourceDirection = SourceDirection}
    {algebra = algebra} {calculus = calculus}
    {published = published} {meaning = meaning}
    round281 →
  E4.LocalCStressRound281Selection
    {G = G} {X = X} {Configuration = Configuration}
    {Position = Position} {CurvaturePolynomial = CurvaturePolynomial}
    {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
    {StressTensor = Top.StressTensor C}
    {Hilbert = Hilbert} {Vector = Vector}
    {Hamiltonian = Hamiltonian} {Algebra = Algebra}
    {Scale = Scale} {Volume = Volume} {Root = Root}
    {ContinuumFamily = ContinuumFamily} {Core = Core}
    {Observable = Configuration → ℝ}
    {Scalar = Scalar} {SourceDirection = SourceDirection}
    {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
    {quotient = quotient} {division = division} {S = osS}
    {osInputs = osInputs} {reconstruction = reconstruction} {group = group}
    {algebra = algebra} {calculus = calculus}
    {published = published} {meaning = meaning}
    localC round281
asRound281StressSelection shared = record
  { E4.LocalCStressRound281Selection.stressObservableOf =
      E2.encodeStress (cylinderEmbedding shared)
  }

selectedE4FromSharedE2Observable :
  ∀ {C S Y group
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division osS osInputs reconstruction
      localC Scalar SourceDirection algebra calculus published meaning round281}
    (shared :
      SharedPinnedStressObservable
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
        {Scalar = Scalar} {SourceDirection = SourceDirection}
        {algebra = algebra} {calculus = calculus}
        {published = published} {meaning = meaning}
        round281) →
  E4.SelectedMarkedE4
    (R281.asRound279SpatialShell round281)
    (E2.encodeStress (cylinderEmbedding shared) (LocalC.stressTensor localC))
selectedE4FromSharedE2Observable shared =
  E4.selectedMarkedE4 (asRound281StressSelection shared)

e2AndE4ShareExactlyOneStressObservableMap : Bool
e2AndE4ShareExactlyOneStressObservableMap = true

e4NeedsIndependentStressObservableSelection : Bool
e4NeedsIndependentStressObservableSelection = false

e4NeedsIndependentDecayEstimateAfterSharedEncoding : Bool
e4NeedsIndependentDecayEstimateAfterSharedEncoding = false

remainingSharedE2E4PhysicalLeafIsCylinderEncodingAndAdmissibility : Bool
remainingSharedE2E4PhysicalLeafIsCylinderEncodingAndAdmissibility = true
