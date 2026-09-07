module DASHI.Physics.Closure.NSTriadKNPhysicalGramOperatorPaymentRound472Exact where

------------------------------------------------------------------------
-- ROUND472 / PREFERRED GRAM CONSUMER -> ACTUAL R432 FIXED-OUTPUT PAYMENT
--
-- Lean sibling provenance (2026-09-07):
--   RequestProject/NavierStokes/OperatorSchurBlockCancellation.lean
--   RequestProject/NavierStokes/TransverseFrameSplit.lean
--
-- R471 makes the fixed-output Gram l2->l2 bound the primitive consumer.  This
-- owner welds that primitive theorem shape back to the live Agda remainder
-- compiler R432.
--
-- The same-object seam is explicit: a physical snapshot identifies
--
--   R432 signedCross = gramQuadratic(coeff)
--   R432 fibreBudget = A * coeffMass(coeff).
--
-- Once those equalities are supplied, ANY R471 producer pays R432.  In
-- particular two scalar polarization bounds first compile through R471 and then
-- pay the same R432 consumer.  Absolute Schur is nowhere required.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNFixedOutputSignedCrossAggregationRound432Exact as R432
import DASHI.Physics.Closure.NSTriadKNGramOperatorBoundConsumerRound471Exact as R471

------------------------------------------------------------------------
-- Same-object snapshot from the physical fixed-output carrier to the generic
-- Gram consumer.
------------------------------------------------------------------------

record PhysicalFixedOutputGramSnapshot
    (Coeff : Set)
    (gramQuadratic coeffMass : Coeff → ℚ)
    (A : ℚ) : Set where
  constructor physical-fixed-output-gram-snapshot
  field
    coeff : Coeff
    signedCross fibreBudget : ℚ

    signedCrossMeaning :
      signedCross ≡ gramQuadratic coeff

    fibreBudgetMeaning :
      fibreBudget ≡ A * coeffMass coeff

open PhysicalFixedOutputGramSnapshot public

gramBoundPaysPhysicalSnapshot :
  ∀ {Coeff gramQuadratic coeffMass A} →
  R471.GramOperatorBound Coeff gramQuadratic coeffMass A →
  (S : PhysicalFixedOutputGramSnapshot Coeff gramQuadratic coeffMass A) →
  R432.FixedOutputSignedCrossPayment
gramBoundPaysPhysicalSnapshot B S = record
  { R432.signedCross = signedCross S
  ; R432.fibreBudget = fibreBudget S
  ; R432.signedCrossBound =
      subst
        (λ lower → lower ≤ fibreBudget S)
        (sym (signedCrossMeaning S))
        (subst
          ((gramQuadratic (coeff S)) ≤_)
          (sym (fibreBudgetMeaning S))
          (R471.quadraticBound B (coeff S)))
  }

------------------------------------------------------------------------
-- Physical two-polarization producer.  The split is exact; the two scalar
-- bounds are the only analytic producer leaves.
------------------------------------------------------------------------

record PhysicalTwoPolarizationGramProducer
    (Coeff : Set)
    (totalGram firstGram secondGram : Coeff → ℚ)
    (totalMass firstMass secondMass : Coeff → ℚ)
    (A : ℚ) : Set where
  constructor physical-two-polarization-gram-producer
  field
    exactSplit :
      R471.TwoPolarizationSplit
        Coeff totalGram firstGram secondGram
        totalMass firstMass secondMass

    firstScalarGramBound :
      R471.GramOperatorBound Coeff firstGram firstMass A

    secondScalarGramBound :
      R471.GramOperatorBound Coeff secondGram secondMass A

open PhysicalTwoPolarizationGramProducer public

physicalTwoPolarizationProducerToGramBound :
  ∀ {Coeff totalGram firstGram secondGram totalMass firstMass secondMass A} →
  PhysicalTwoPolarizationGramProducer
    Coeff totalGram firstGram secondGram totalMass firstMass secondMass A →
  R471.GramOperatorBound Coeff totalGram totalMass A
physicalTwoPolarizationProducerToGramBound P =
  R471.twoPolarizationBoundsCompile
    (exactSplit P)
    (firstScalarGramBound P)
    (secondScalarGramBound P)

physicalTwoPolarizationProducerPaysR432 :
  ∀ {Coeff totalGram firstGram secondGram totalMass firstMass secondMass A} →
  (P : PhysicalTwoPolarizationGramProducer
    Coeff totalGram firstGram secondGram totalMass firstMass secondMass A) →
  PhysicalFixedOutputGramSnapshot Coeff totalGram totalMass A →
  R432.FixedOutputSignedCrossPayment
physicalTwoPolarizationProducerPaysR432 P =
  gramBoundPaysPhysicalSnapshot
    (physicalTwoPolarizationProducerToGramBound P)

------------------------------------------------------------------------
-- Uniform family shape: the SAME constant A is used for every retained output.
-- Output-dependent scalar forms are carried by a producer selected at output.
------------------------------------------------------------------------

record UniformOutputGramProducer
    (Output Coeff : Set)
    (A : ℚ)
    (totalGram totalMass : Output → Coeff → ℚ) : Set₁ where
  constructor uniform-output-gram-producer
  field
    gramBoundAt :
      (output : Output) →
      R471.GramOperatorBound Coeff
        (totalGram output) (totalMass output) A

open UniformOutputGramProducer public

uniformOutputProducerPaysSnapshot :
  ∀ {Output Coeff A totalGram totalMass} →
  (P : UniformOutputGramProducer Output Coeff A totalGram totalMass) →
  (output : Output) →
  PhysicalFixedOutputGramSnapshot
    Coeff (totalGram output) (totalMass output) A →
  R432.FixedOutputSignedCrossPayment
uniformOutputProducerPaysSnapshot P output =
  gramBoundPaysPhysicalSnapshot (gramBoundAt P output)

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round472GramBoundToR432CompilerClosed : Bool
round472GramBoundToR432CompilerClosed = true

round472TwoPolarizationToR432CompilerClosed : Bool
round472TwoPolarizationToR432CompilerClosed = true

round472UniformOutputConstantIsShared : Bool
round472UniformOutputConstantIsShared = true

round472LiteralOuterCellSnapshotWeldClosed : Bool
round472LiteralOuterCellSnapshotWeldClosed = false

round472FirstPhysicalScalarPolarizationBoundClosed : Bool
round472FirstPhysicalScalarPolarizationBoundClosed = false

round472SecondPhysicalScalarPolarizationBoundClosed : Bool
round472SecondPhysicalScalarPolarizationBoundClosed = false

round472PackageAClosed : Bool
round472PackageAClosed = false

round472ClayPromotion : Bool
round472ClayPromotion = false

round472GramBoundToR432CompilerClosedIsTrue :
  round472GramBoundToR432CompilerClosed ≡ true
round472GramBoundToR432CompilerClosedIsTrue = refl

round472LiteralOuterCellSnapshotWeldClosedIsFalse :
  round472LiteralOuterCellSnapshotWeldClosed ≡ false
round472LiteralOuterCellSnapshotWeldClosedIsFalse = refl
