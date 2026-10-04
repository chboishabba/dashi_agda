{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyMarkedStressE2CylinderEmbeddingExact where

------------------------------------------------------------------------
-- MARKED E2 FROM INCLUSION IN THE EXISTING OS CYLINDER ALGEBRA.
--
-- The current CMP119 OS2 theorem already proves nonnegativity of every finite
-- reflected Gram quadratic form on the physical cylinder observable algebra and
-- transports that positivity to the continuum limit.
--
-- Therefore a stress-marked extension does NOT need a new positivity estimate.
-- It needs an admissible embedding of the stress mark into that same algebra:
--
--   encodeStress : StressMark -> Observable
--
-- compatible with reflection and carrying positive-time / gauge-invariant
-- admissibility.  Once this is supplied, any finite stress-marked family
-- decodes to an ordinary OS cylinder family and existing continuum OS2 applies.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _≤ℝ_)

import DASHI.Physics.YangMills.YangMillsCylinderLimitOSReflectionPositiveExact as OS2
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5OSGramTopologyExact as OSTop
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanScalarCylinderExpectationLimitExact as Cylinder

record MarkedStressCylinderEmbedding
    (Observable StressMark : Set)
    (observableAlgebra : OS2.CylinderOSAlgebra Observable)
    : Set₁ where
  field
    encodeStress :
      StressMark → Observable

    PositiveTimeSupported :
      Observable → Set

    GaugeInvariantObservable :
      Observable → Set

    stressPositiveTime :
      ∀ mark →
      PositiveTimeSupported (encodeStress mark)

    stressGaugeInvariant :
      ∀ mark →
      GaugeInvariantObservable (encodeStress mark)

    reflectStressMark :
      StressMark → StressMark

    encodeCommutesWithReflection :
      ∀ mark →
      encodeStress (reflectStressMark mark)
      ≡
      OS2.reflectObservable observableAlgebra
        (encodeStress mark)

open MarkedStressCylinderEmbedding public

record MarkedStressPositiveTimeTest
    {Observable StressMark : Set}
    {observableAlgebra : OS2.CylinderOSAlgebra Observable}
    (embedding :
      MarkedStressCylinderEmbedding
        Observable StressMark observableAlgebra)
    : Set₁ where
  constructor markedStressTest
  field
    stressMark :
      StressMark

    coefficient :
      ℝ

open MarkedStressPositiveTimeTest public

record MarkedStressFiniteTestFamily
    {Observable StressMark : Set}
    {observableAlgebra : OS2.CylinderOSAlgebra Observable}
    (embedding :
      MarkedStressCylinderEmbedding
        Observable StressMark observableAlgebra)
    : Set₁ where
  constructor markedStressFamily
  field
    tests :
      List (MarkedStressPositiveTimeTest embedding)

open MarkedStressFiniteTestFamily public

decodeMarkedStressTest :
  ∀ {Observable StressMark observableAlgebra}
    {embedding :
      MarkedStressCylinderEmbedding
        Observable StressMark observableAlgebra} →
  MarkedStressPositiveTimeTest embedding →
  Gram.PhysicalPositiveTimeCylinderTest Observable ℝ
decodeMarkedStressTest {embedding = embedding} test =
  Gram.cylinderTest
    (encodeStress embedding (stressMark test))
    (coefficient test)
    (PositiveTimeSupported embedding
      (encodeStress embedding (stressMark test)))
    (GaugeInvariantObservable embedding
      (encodeStress embedding (stressMark test)))

decodeMarkedStressTests :
  ∀ {Observable StressMark observableAlgebra}
    {embedding :
      MarkedStressCylinderEmbedding
        Observable StressMark observableAlgebra} →
  List (MarkedStressPositiveTimeTest embedding) →
  List (Gram.PhysicalPositiveTimeCylinderTest Observable ℝ)
decodeMarkedStressTests [] = []
decodeMarkedStressTests (test ∷ rest) =
  decodeMarkedStressTest test ∷ decodeMarkedStressTests rest

decodeMarkedStressFamily :
  ∀ {Observable StressMark observableAlgebra}
    {embedding :
      MarkedStressCylinderEmbedding
        Observable StressMark observableAlgebra} →
  MarkedStressFiniteTestFamily embedding →
  Gram.PhysicalOSFiniteTestFamily Observable ℝ
decodeMarkedStressFamily family =
  Gram.finiteTestFamily
    (decodeMarkedStressTests (tests family))

markedContinuumReflectionPositive :
  ∀ {Observable StressMark sequenceLimit}
    {limitLaws :
      RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {cylinder :
      Cylinder.ScalarCylinderExpectationLimitData
        Observable ℝ
        (RealLimit.canonicalCylinderAlgebra limitLaws)}
    {observableAlgebra :
      OS2.CylinderOSAlgebra Observable}
    (inputs :
      OS2.CylinderLimitOSInputs
        limitLaws cylinder observableAlgebra)
    (embedding :
      MarkedStressCylinderEmbedding
        Observable StressMark observableAlgebra)
    (family :
      MarkedStressFiniteTestFamily embedding) →
  0ℝ ≤ℝ
    Gram.physicalReflectedGramQuadraticForm
      (OS2.operations observableAlgebra)
      (Cylinder.limitExpectation cylinder)
      (decodeMarkedStressFamily family)
markedContinuumReflectionPositive inputs embedding family =
  OS2.continuumReflectionPositive inputs
    (decodeMarkedStressFamily family)

markedE2NeedsNoNewGramEstimate : Bool
markedE2NeedsNoNewGramEstimate = true

markedE2ResidualIsStressCylinderEmbedding : Bool
markedE2ResidualIsStressCylinderEmbedding = true

reflectionCompatibilityExplicitInEmbedding : Bool
reflectionCompatibilityExplicitInEmbedding = true
