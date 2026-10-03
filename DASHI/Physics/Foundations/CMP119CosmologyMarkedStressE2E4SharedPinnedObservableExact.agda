{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyMarkedStressE2E4SharedPinnedObservableExact where

------------------------------------------------------------------------
-- ONE PINNED LOCAL-C STRESS OBSERVABLE FOR BOTH E2 AND E4.
--
-- E2 already requires an encoding
--
--   StressTensor -> Configuration -> R
--
-- into the pinned OS cylinder algebra.  Round281 E4 only needs a selected
-- Local-C stress observable.  Do not choose that observable independently:
-- reuse the E2 encoding definitionally.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressE2PinnedOSAlgebraExact as E2
import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressE4Round281Exact as E4
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as LocalC
import DASHI.Physics.YangMills.BalabanCMP116119NormalizedExpectationDerivativeRound281Exact as R281
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant

asRound281StressSelection :
  ∀ {C S}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    {G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient Hilbert Vector Hamiltonian Algebra
     Scale Volume Root ContinuumFamily Core Scalar SourceDirection : Set}
    {sequenceLimit limitLaws quotient division osS osInputs reconstruction}
    {localC :
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
        osInputs reconstruction group}
    {algebra : Cumulant.TwoSourceMomentAlgebra (Configuration → ℝ) Scalar}
    {calculus : Cumulant.NormalizedLogSourceCalculus algebra}
    {published : R281.CMP116119PublishedTwoSourceLocalization Scale Volume Root}
    {meaning : Cumulant.LiteralTwoSourceInsertionMeaning calculus SourceDirection}
    {round281 : R281.LiteralTwoSourceNormalizedExpectationWeld published meaning} →
  E2.PinnedLocalCStressCylinderEmbedding Y group localC →
  E4.LocalCStressRound281Selection localC round281
asRound281StressSelection embedding = record
  { E4.LocalCStressRound281Selection.stressObservableOf =
      E2.encodeStress embedding
  }

selectedE2StressObservableIsSelectedE4StressObservable :
  ∀ {C S}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    {G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient Hilbert Vector Hamiltonian Algebra
     Scale Volume Root ContinuumFamily Core Scalar SourceDirection : Set}
    {sequenceLimit limitLaws quotient division osS osInputs reconstruction}
    {localC :
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
        osInputs reconstruction group}
    {algebra : Cumulant.TwoSourceMomentAlgebra (Configuration → ℝ) Scalar}
    {calculus : Cumulant.NormalizedLogSourceCalculus algebra}
    {published : R281.CMP116119PublishedTwoSourceLocalization Scale Volume Root}
    {meaning : Cumulant.LiteralTwoSourceInsertionMeaning calculus SourceDirection}
    {round281 : R281.LiteralTwoSourceNormalizedExpectationWeld published meaning}
    (embedding : E2.PinnedLocalCStressCylinderEmbedding Y group localC) →
  E4.selectedStressObservable (asRound281StressSelection embedding)
  ≡ E2.encodeStress embedding (LocalC.stressTensor localC)
selectedE2StressObservableIsSelectedE4StressObservable embedding = refl

independentE4StressObservableChoiceEliminated : Bool
independentE4StressObservableChoiceEliminated = true

remainingE2E4LeavesAreAdmissibilityReflectionAndOS4Semantics : Bool
remainingE2E4LeavesAreAdmissibilityReflectionAndOS4Semantics = true
