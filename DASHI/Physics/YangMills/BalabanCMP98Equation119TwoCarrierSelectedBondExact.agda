{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119TwoCarrierSelectedBondExact where

------------------------------------------------------------------------
-- CMP98 EQ. (119): TWO-CARRIER SELECTED-BOND COMPILER
--
-- Primary source:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- R147 used one abstract Vector both for
--   * the global perturbation A supplied to Q', and
--   * the local Lie value carried by each R0 path and by the selected coarse
--     bond output.
--
-- The literal equation-(119) formula does not require those types to coincide.
-- This owner repeats the checked finite path/block calculation with distinct
-- carriers:
--
--   GlobalPerturbation --bondComponent--> LocalLie
--
-- and computes one selected coarse-bond derivative
--
--   GlobalPerturbation -> LocalLie.
--
-- A family indexed by coarse bonds then assembles these local values into the
-- corresponding coarse-bond field.  No function extensionality or continuum
-- input is needed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (_++_)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralPathRound147Exact as R147
import DASHI.Physics.YangMills.BalabanCMP98TranslatedCrossingFromCentreRound150Exact as R150
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ShortestContourEnumerationExact as Contours
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Blocks
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Word

record TwoCarrierEquation119PathData
    (Local : R146.SignedAdditiveOperatorCarrier)
    (Global Value : Set)
    (n : Nat)
    (group : Bond.ExactLinkGroup Value) : Set₁ where
  field
    realization : Nat → Bond.PeriodicBondGaugeRealization n Value group

    bondComponent :
      Nat → Global → Blocks.PeriodicBlock n → Word.SignedAxis4 →
      R126.Vector (R146.additive Local)

    adjointLink :
      Nat → Value → R126.Operator (R146.additive Local)

    scaleV : ℚ → R126.Operator (R146.additive Local)

    minusEmbedding plusEmbedding :
      Nat → Embed.CenteredPeriodicNoWrapEmbedding n 6

    coarseSegment : Nat → Contours.AxisSegment

    coarseSegmentEndsAtPlusCentre : ∀ step →
      Bond.walk
        (Embed.embeddingCentre (minusEmbedding step))
        (Periodic.segmentWord (coarseSegment step))
      ≡ Embed.embeddingCentre (plusEmbedding step)

    translationCommutation : Embed.PeriodicSegmentCommutation n

    dexpMinusOuter : Nat → R126.Operator (R146.additive Local)
    inverseDexpMinusAt :
      Nat → Centered.CenteredBlockPoint4 6 →
      R126.Operator (R146.additive Local)
    adjointExpAt :
      Nat → Centered.CenteredBlockPoint4 6 →
      R126.Operator (R146.additive Local)
    adjointExpOuter : Nat → R126.Operator (R146.additive Local)

open TwoCarrierEquation119PathData public

coarseWord :
  ∀ {Local Global Value n group} →
  TwoCarrierEquation119PathData Local Global Value n group →
  Nat → List Word.SignedAxis4
coarseWord dataSet step = Periodic.segmentWord (coarseSegment dataSet step)

plusOffset :
  ∀ {Local Global Value n group} →
  TwoCarrierEquation119PathData Local Global Value n group →
  Nat → Centered.CenteredBlockPoint4 6 → Centered.CenteredBlockPoint4 6
plusOffset dataSet step point = point

translatedGeometryAt :
  ∀ {Local Global Value n group} →
  TwoCarrierEquation119PathData Local Global Value n group →
  Nat → R150.TranslatedNeighbourBlockSegment n 6
translatedGeometryAt dataSet step = record
  { R150.TranslatedNeighbourBlockSegment.commutation =
      translationCommutation dataSet
  ; R150.TranslatedNeighbourBlockSegment.minusEmbedding =
      minusEmbedding dataSet step
  ; R150.TranslatedNeighbourBlockSegment.plusEmbedding =
      plusEmbedding dataSet step
  ; R150.TranslatedNeighbourBlockSegment.coarseSegment =
      coarseSegment dataSet step
  ; R150.TranslatedNeighbourBlockSegment.plusCentreIsCoarseSegment =
      coarseSegmentEndsAtPlusCentre dataSet step
  }

crossingHitsPlusOffset :
  ∀ {Local Global Value n group}
    (dataSet : TwoCarrierEquation119PathData Local Global Value n group)
    step point →
  Bond.walk
    (Embed.embed (minusEmbedding dataSet step) point)
    (coarseWord dataSet step)
  ≡ Embed.embed (plusEmbedding dataSet step) (plusOffset dataSet step point)
crossingHitsPlusOffset dataSet step point =
  R150.radiusSixTranslatedSegmentHitsSameOffset
    (translatedGeometryAt dataSet step) point

r0Path :
  ∀ {Local Global Value n group} →
  TwoCarrierEquation119PathData Local Global Value n group →
  Nat → Global → Blocks.PeriodicBlock n → List Word.SignedAxis4 →
  R126.Vector (R146.additive Local)
r0Path {Local} dataSet step A site [] =
  R126.zeroV (R146.additive Local)
r0Path {Local} dataSet step A site (direction ∷ directions) =
  R126.addV (R146.additive Local)
    (bondComponent dataSet step A site direction)
    (adjointLink dataSet step
      (Bond.orientedLink (realization dataSet step) site direction)
      (r0Path dataSet step A
        (Bond.walkStep site direction) directions))

minusToCrossingWord :
  ∀ {Local Global Value n group} →
  TwoCarrierEquation119PathData Local Global Value n group →
  Nat → Centered.CenteredBlockPoint4 6 → List Word.SignedAxis4
minusToCrossingWord dataSet step point =
  Embed.canonicalCenteredContourWord point ++ coarseWord dataSet step

plusFullWord :
  ∀ {Local Global Value n group} →
  TwoCarrierEquation119PathData Local Global Value n group →
  Nat → Centered.CenteredBlockPoint4 6 → List Word.SignedAxis4
plusFullWord dataSet step point =
  coarseWord dataSet step
  ++ Embed.canonicalCenteredContourWord (plusOffset dataSet step point)

centreWord :
  ∀ {Local Global Value n group} →
  TwoCarrierEquation119PathData Local Global Value n group →
  Nat → List Word.SignedAxis4
centreWord = coarseWord

minusToCrossingEndpointExact :
  ∀ {Local Global Value n group}
    (dataSet : TwoCarrierEquation119PathData Local Global Value n group)
    step point →
  Bond.walk
    (Embed.embeddingCentre (minusEmbedding dataSet step))
    (minusToCrossingWord dataSet step point)
  ≡ Bond.walk
      (Embed.embed (minusEmbedding dataSet step) point)
      (coarseWord dataSet step)
minusToCrossingEndpointExact dataSet step point =
  trans
    (Embed.walkAppend
      (Embed.embeddingCentre (minusEmbedding dataSet step))
      (Embed.canonicalCenteredContourWord point)
      (coarseWord dataSet step))
    (cong
      (λ site → Bond.walk site (coarseWord dataSet step))
      (sym (Embed.embedMeaning (minusEmbedding dataSet step) point)))

plusFullEndpointExact :
  ∀ {Local Global Value n group}
    (dataSet : TwoCarrierEquation119PathData Local Global Value n group)
    step point →
  Bond.walk
    (Embed.embeddingCentre (minusEmbedding dataSet step))
    (plusFullWord dataSet step point)
  ≡ Embed.embed (plusEmbedding dataSet step) (plusOffset dataSet step point)
plusFullEndpointExact dataSet step point =
  trans
    (Embed.walkAppend
      (Embed.embeddingCentre (minusEmbedding dataSet step))
      (coarseWord dataSet step)
      (Embed.canonicalCenteredContourWord (plusOffset dataSet step point)))
    (trans
      (cong
        (λ site →
          Bond.walk site
            (Embed.canonicalCenteredContourWord (plusOffset dataSet step point)))
        (coarseSegmentEndsAtPlusCentre dataSet step))
      (sym
        (Embed.embedMeaning
          (plusEmbedding dataSet step)
          (plusOffset dataSet step point))))

sourceLegsShareEndpoint :
  ∀ {Local Global Value n group}
    (dataSet : TwoCarrierEquation119PathData Local Global Value n group)
    step point →
  Bond.walk
    (Embed.embeddingCentre (minusEmbedding dataSet step))
    (minusToCrossingWord dataSet step point)
  ≡ Bond.walk
      (Embed.embeddingCentre (minusEmbedding dataSet step))
      (plusFullWord dataSet step point)
sourceLegsShareEndpoint dataSet step point =
  trans
    (minusToCrossingEndpointExact dataSet step point)
    (trans
      (crossingHitsPlusOffset dataSet step point)
      (sym (plusFullEndpointExact dataSet step point)))

pointTerm :
  ∀ {Local Global Value n group} →
  TwoCarrierEquation119PathData Local Global Value n group →
  Nat → Global → Centered.CenteredBlockPoint4 6 →
  R126.Vector (R146.additive Local)
pointTerm {Local} dataSet step A point =
  scaleV dataSet R147.siteWeightℚ
    (inverseDexpMinusAt dataSet step point
      (R146.subV
        (r0Path dataSet step A
          (Embed.embeddingCentre (minusEmbedding dataSet step))
          (minusToCrossingWord dataSet step point))
        (adjointExpAt dataSet step point
          (r0Path dataSet step A
            (Embed.embeddingCentre (minusEmbedding dataSet step))
            (plusFullWord dataSet step point)))))

pointTerms :
  ∀ {Local Global Value n group} →
  TwoCarrierEquation119PathData Local Global Value n group →
  Nat → Global → List (Centered.CenteredBlockPoint4 6) →
  List (R126.Vector (R146.additive Local))
pointTerms dataSet step A [] = []
pointTerms dataSet step A (point ∷ points) =
  pointTerm dataSet step A point ∷ pointTerms dataSet step A points

literalBlockContribution :
  ∀ {Local Global Value n group} →
  TwoCarrierEquation119PathData Local Global Value n group →
  Nat → Global → R126.Vector (R146.additive Local)
literalBlockContribution dataSet step A =
  R146.sumV
    (pointTerms dataSet step A
      (Carrier.elements (Centered.centeredBlockFinite 6)))

selectedEquation119QPrime :
  ∀ {Local Global Value n group} →
  TwoCarrierEquation119PathData Local Global Value n group →
  Nat → Global → R126.Vector (R146.additive Local)
selectedEquation119QPrime {Local} dataSet step A =
  R126.addV (R146.additive Local)
    (dexpMinusOuter dataSet step (literalBlockContribution dataSet step A))
    (adjointExpOuter dataSet step
      (r0Path dataSet step A
        (Embed.embeddingCentre (minusEmbedding dataSet step))
        (centreWord dataSet step)))

------------------------------------------------------------------------
-- Assemble selected-bond values into a coarse-bond field.
------------------------------------------------------------------------

record TwoCarrierEquation119FieldFamily
    (Local : R146.SignedAdditiveOperatorCarrier)
    (Global CoarseBond Value : Set)
    (n : Nat)
    (group : Bond.ExactLinkGroup Value) : Set₁ where
  field
    sourceAt : CoarseBond →
      TwoCarrierEquation119PathData Local Global Value n group

open TwoCarrierEquation119FieldFamily public

assembledEquation119QPrime :
  ∀ {Local Global CoarseBond Value n group} →
  TwoCarrierEquation119FieldFamily Local Global CoarseBond Value n group →
  Nat → Global → CoarseBond → R126.Vector (R146.additive Local)
assembledEquation119QPrime family step A coarseBond =
  selectedEquation119QPrime (sourceAt family coarseBond) step A

assembledEquation119QPrimeAtBondExact :
  ∀ {Local Global CoarseBond Value n group}
    (family : TwoCarrierEquation119FieldFamily
      Local Global CoarseBond Value n group)
    step A coarseBond →
  assembledEquation119QPrime family step A coarseBond
  ≡ selectedEquation119QPrime (sourceAt family coarseBond) step A
assembledEquation119QPrimeAtBondExact family step A coarseBond = refl

cmp98Equation119TwoCarrierR0CompilerLevel : ProofLevel
cmp98Equation119TwoCarrierR0CompilerLevel = machineChecked

cmp98Equation119TwoCarrierSelectedBondLevel : ProofLevel
cmp98Equation119TwoCarrierSelectedBondLevel = machineChecked

cmp98Equation119TwoCarrierFieldAssemblyLevel : ProofLevel
cmp98Equation119TwoCarrierFieldAssemblyLevel = machineChecked
