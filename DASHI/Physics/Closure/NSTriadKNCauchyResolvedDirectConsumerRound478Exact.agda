module DASHI.Physics.Closure.NSTriadKNCauchyResolvedDirectConsumerRound478Exact where

------------------------------------------------------------------------
-- ROUND478 / WEAKEST CAUCHY-RESOLVED FIXED-OUTPUT CONSUMER
--
-- R471 deliberately distinguishes the primitive fixed-output GramOperatorBound
-- from stronger sufficient producer certificates.  R477 installs the literal
-- nonseparable Cauchy pair kernel and proves that TWO same-helicity scalar
-- resolved bounds compile to the full physical resolved bound.
--
-- The converse is not required by the consumer.  Therefore the shortest
-- theorem target is the single total resolved GramOperatorBound itself:
--
--   Q_resolved(c) <= A * M(c).
--
-- Proving the + and - inequalities separately is a sufficient producer route,
-- but it is stronger search structure than the final consumer asks for.  This
-- owner makes that least-privilege distinction explicit so proof search can
-- retain any compensation visible only after the two helical pieces are summed.
--
-- No physical operator bound is manufactured here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedGramOperatorRound477Exact as R477

F : C3.RealField _
F = Rational.rationalRealField

DirectResolvedPhysicalGramBound :
  ∀ {Index} →
  R477.CauchyResolvedCellFamily Index → ℚ → Set
DirectResolvedPhysicalGramBound = R477.ResolvedGramOperatorBound

record SplitResolvedScalarProducer
    {Index : Set}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (k : Z3.FourierMode)
    (family : R477.CauchyResolvedCellFamily Index)
    (A : ℚ) : Set where
  constructor split-resolved-scalar-producer
  field
    plusBound :
      R477.ResolvedGramOperatorBound
        (R477.plusFamily E I S k family) A
    minusBound :
      R477.ResolvedGramOperatorBound
        (R477.minusFamily E I S k family) A

open SplitResolvedScalarProducer public

splitProducerCompilesToDirectConsumer :
  ∀ {Index}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (k : Z3.FourierMode)
    (family : R477.CauchyResolvedCellFamily Index)
    (transverse : R477.AllIndexedTransverse E k family)
    (A : ℚ) →
  SplitResolvedScalarProducer E I S k family A →
  DirectResolvedPhysicalGramBound family A
splitProducerCompilesToDirectConsumer
    E I S L k family transverse A producer =
  R477.scalarResolvedBoundsCompile
    E I S L k family transverse A
    (plusBound producer)
    (minusBound producer)

------------------------------------------------------------------------
-- Search / trust boundary.
--
-- `round478DirectResolvedConsumerPreferred = true` does NOT say that the
-- physical bound is proved.  It says only that this is the weakest current
-- theorem target.  The split producer remains available as a sufficient route.
------------------------------------------------------------------------

round478DirectResolvedConsumerPreferred : Bool
round478DirectResolvedConsumerPreferred = true

round478SplitScalarPairIsSufficientProducer : Bool
round478SplitScalarPairIsSufficientProducer = true

round478SplitScalarPairIsMandatory : Bool
round478SplitScalarPairIsMandatory = false

round478PhysicalDirectResolvedBoundClosed : Bool
round478PhysicalDirectResolvedBoundClosed = false

round478PackageAClosed : Bool
round478PackageAClosed = false

round478ClayPromotion : Bool
round478ClayPromotion = false

round478SplitScalarPairIsMandatoryIsFalse :
  round478SplitScalarPairIsMandatory ≡ false
round478SplitScalarPairIsMandatoryIsFalse = refl

round478PhysicalDirectResolvedBoundClosedIsFalse :
  round478PhysicalDirectResolvedBoundClosed ≡ false
round478PhysicalDirectResolvedBoundClosedIsFalse = refl
