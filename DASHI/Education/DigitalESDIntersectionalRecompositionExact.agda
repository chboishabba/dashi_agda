module DASHI.Education.DigitalESDIntersectionalRecompositionExact where

------------------------------------------------------------------------
-- DIGITAL-ESD N-AXIS RECOMPOSITION: ACTUAL PROOF TERMS, NOT BOOL FLAGS
--
-- Attribution and reuse:
--   DASHI.Core.IntersectionalNonFactorability (Crenshaw 1991, DOI
--   10.2307/1229039, motivates the situated-visibility question; the
--   mathematical witness is an independent DASHI construction).
--   DASHI.Reasoning.TypedHyperfabricCore (Duta, Cassarà, Silvestri, Liò,
--   "Sheaf Hypergraph Networks", arXiv:2309.17116, structural donor only).
--   DASHI.Education.DigitalESDOpenAxisStudyPartWorldExact (local ESD owner).
--
-- Source study observations and conclusions are never introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Education.DigitalESDGoldenIntersectionalKernelExact as Golden
import DASHI.Core.IntersectionalNonFactorability as Factor
import DASHI.Reasoning.TypedHyperfabricCore as Hyper
import DASHI.Education.DigitalESDOpenAxisStudyPartWorldExact as World

------------------------------------------------------------------------
-- XR00: a manuscript/world projection cannot claim "no lost information"
-- from a string receipt or injectivity of source IDs. It must exhibit
-- a reconstruction map and a round-trip proof on the actual same object.
------------------------------------------------------------------------

record LosslessRecomposition
  {Situated Summary : Set}
  (project : Situated → Summary) : Set where
  constructor lossless-recomposition
  field
    recover : Summary → Situated
    recoverAfterProject :
      (situated : Situated) → recover (project situated) ≡ situated

open LosslessRecomposition public

-- XR01: a genuinely lossless projection is injective on situated worlds.
sameSummaryImpliesSameSituated :
  {Situated Summary : Set} →
  (project : Situated → Summary) →
  LosslessRecomposition project →
  (left right : Situated) →
  project left ≡ project right → left ≡ right
sameSummaryImpliesSameSituated project cert left right same =
  trans (sym (recoverAfterProject cert left))
    (trans (cong (recover cert) same)
      (recoverAfterProject cert right))

-- The Golden --safe core is the mathematical theorem owner. This adapter
-- preserves the pre-existing ESD/IntersectionalNonFactorability types.
asGoldenLossless :
  {Situated Summary : Set} →
  {project : Situated → Summary} →
  LosslessRecomposition project →
  Golden.Lossless project
asGoldenLossless cert =
  Golden.lossless (recover cert) (recoverAfterProject cert)

-- XR02: any consumer of the original situated world factors through a
-- truly lossless summary. Merely having an axis table never proves this.
losslessSufficesForConsumer :
  {Situated Summary Outcome : Set} →
  (project : Situated → Summary) →
  (consumer : Situated → Outcome) →
  LosslessRecomposition project →
  Factor.FactorsThrough project consumer
losslessSufficesForConsumer project consumer cert =
  Factor.factorsThrough
    (Golden.interpret goldenFactor)
    (Golden.factors goldenFactor)
  where
    goldenFactor : Golden.FactorsThrough project consumer
    goldenFactor =
      Golden.losslessConsumerFactorisation
        project consumer (asGoldenLossless cert)

-- XR03: a real source-specific non-factorability witness forbids claiming
-- lossless recomposition. This uses the *existing* intersectional theorem.
nonFactorabilityBlocksLosslessRecomposition :
  {Situated Summary Outcome : Set} →
  (project : Situated → Summary) →
  (consumer : Situated → Outcome) →
  Factor.NonFactorabilityWitness project consumer →
  LosslessRecomposition project → ⊥
nonFactorabilityBlocksLosslessRecomposition project consumer witness cert =
  Factor.witnessRulesOutEveryFlatFactorisation witness
    (losslessSufficesForConsumer project consumer cert)

-- XR04: concrete finite negative control, explicitly SYNTHETIC, inherited
-- from the canonical DASHI intersectional collision. It is not evidence
-- of an interaction measured in any Alice/ESD/EfS study.
canonicalIntersectionalFlatCannotRecompose :
  LosslessRecomposition Factor.flatProjection → ⊥
canonicalIntersectionalFlatCannotRecompose =
  nonFactorabilityBlocksLosslessRecomposition
    Factor.flatProjection
    Factor.relationalOutcome
    Factor.canonicalIntersectionalNonFactorability

------------------------------------------------------------------------
-- XR05: on the actual TypedHyperfabric vertex stalk, every possible
-- declared axis-valuation function must survive encode/decode pointwise.
-- A readout that ignores its stalk input cannot satisfy roundTrip for
-- distinct evidence states; empty-string provenance receipts cannot pay it.
------------------------------------------------------------------------

record AxisFaithfulStalk
  (scope : World.StudyWorldScope)
  (world : World.AccountedStudyWorld scope)
  (Vertex Edge : Set)
  (fabric : Hyper.TypedHyperfabric Vertex Edge)
  (locate : World.StudyPart scope → Vertex) : Set₂ where
  constructor axis-faithful-stalk
  field
    encodePartAxes :
      (part : World.StudyPart scope) →
      ((axis : World.Axis scope) →
        World.PartAxisAccounting scope
          (World.study part) (World.part part) axis) →
      Hyper.vertexStalk fabric (locate part)

    decodePartAxes :
      (part : World.StudyPart scope) →
      Hyper.vertexStalk fabric (locate part) →
      ((axis : World.Axis scope) →
        World.PartAxisAccounting scope
          (World.study part) (World.part part) axis)

    -- No extensional function equality assumed: each axis is witnessed.
    everyAxisSurvives :
      (part : World.StudyPart scope) →
      (values : (axis : World.Axis scope) →
        World.PartAxisAccounting scope
          (World.study part) (World.part part) axis) →
      (axis : World.Axis scope) →
      decodePartAxes part (encodePartAxes part values) axis ≡ values axis

    actualPartStalk :
      (part : World.StudyPart scope) →
      Hyper.vertexStalk fabric (locate part)

    actualPartAgreesWithWorld :
      (part : World.StudyPart scope) →
      (axis : World.Axis scope) →
      decodePartAxes part (actualPartStalk part) axis ≡
        World.accounting world
          (World.study part) (World.part part) axis

open AxisFaithfulStalk public

-- Same-object bridge: no invented second vertex carrier. Instantiate the
-- standalone Golden source-safe theorem on the *actual* ESD PartAxisAccounting
-- and the *actual* TypedHyperfabric vertex stalk. The section itself remains
-- a separate condition, not something this adapter manufactures.
asGoldenAxisRoundTrip :
  (scope : World.StudyWorldScope) →
  (world : World.AccountedStudyWorld scope) →
  (Vertex Edge : Set) →
  (fabric : Hyper.TypedHyperfabric Vertex Edge) →
  (locate : World.StudyPart scope → Vertex) →
  AxisFaithfulStalk scope world Vertex Edge fabric locate →
  Golden.AllAxisRoundTrip
    (λ part axis → World.PartAxisAccounting scope
      (World.study part) (World.part part) axis)
    (λ part → Hyper.vertexStalk fabric (locate part))
asGoldenAxisRoundTrip scope world Vertex Edge fabric locate cert =
  Golden.all-axis-round-trip
    (encodePartAxes cert)
    (decodePartAxes cert)
    (everyAxisSurvives cert)



-- XR06: the above proof lets the downstream consumer read the exact
-- source-world axis at the recomposed fibre, never just a seven-label view.
recomposedPartReadsSameAxis :
  (scope : World.StudyWorldScope) →
  (world : World.AccountedStudyWorld scope) →
  (Vertex Edge : Set) →
  (fabric : Hyper.TypedHyperfabric Vertex Edge) →
  (locate : World.StudyPart scope → Vertex) →
  (cert : AxisFaithfulStalk scope world Vertex Edge fabric locate) →
  (part : World.StudyPart scope) →
  (axis : World.Axis scope) →
  decodePartAxes cert part (actualPartStalk cert part) axis ≡
    World.accounting world
      (World.study part) (World.part part) axis
recomposedPartReadsSameAxis scope world Vertex Edge fabric locate cert part axis =
  actualPartAgreesWithWorld cert part axis
