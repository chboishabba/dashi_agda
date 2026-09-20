module DASHI.Physics.Closure.NSTriadKNR540PhysicalOffDiagonalR571M2Exact where

------------------------------------------------------------------------
-- PERIODIC B / LITERAL R540 PHYSICAL OFF-DIAGONAL -> PREFERRED R571 M2
--
-- R540 already identifies the literal R396/R385 residual with the ordered
-- off-diagonal sum of the proof-independent physical pair scalar
--
--   symmetricWeightedRemainder(alpha,beta).
--
-- The generic R540->M2 compiler should therefore not leave its carrier abstract.
-- This owner instantiates that compiler on:
--
--   * the ACTUAL physical output fibre;
--   * the ACTUAL R538/R540 pair scalar;
--   * the existing no-duplicate/Unique witness for that fibre.
--
-- Consequently the only remaining hypotheses are the genuinely analytic /
-- same-object ones: construct the R571 sample for each distinct physical pair,
-- prove the literal pair scalar lies below its paired magnitude, and place that
-- sample in one preferred one-sided budget.
--
-- No diagonal completion, fibre-cardinality factor, or absolute-value sum is
-- introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Rational.Base using (ℚ; Positive; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (_≢_; subst)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiberPermutationRound35Exact as Unique
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFiniteWeightedGramFluxAggregationRound385Exact as R385
import DASHI.Physics.Closure.NSTriadKNLiteralR396OrderedOffDiagonalRemainderRound540Exact as R540
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNLuoFinitePairedCommutatorSecondMomentBoundExact as Moment
import DASHI.Physics.Closure.NSTriadKNR571PreferredOneSidedSecondMomentExact as Preferred
import DASHI.Physics.Closure.NSTriadKNR540OffDiagonalToLiteralR571M2Exact as Compiler

F : C3.RealField _
F = Rational.rationalRealField

module PhysicalR540M2
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode)
    (preferred : Preferred.PreferredOneSidedSecondMomentBudget)
    (pairToSample :
      Physical.PhysicalTriadIncidence →
      Physical.PhysicalTriadIncidence →
      Moment.PairedSecondMomentSample)
    (literalPairBelowPairedMagnitude :
      (alpha beta : Physical.PhysicalTriadIncidence) →
      alpha ≢ beta →
      let module O = R540.LiteralOrdered physicalSystem S
      in
      O.Swap.symmetricWeightedRemainder alpha beta
      ≤ Moment.pairedMagnitude (pairToSample alpha beta))
    (sampleInPreferredFamily :
      (alpha beta : Physical.PhysicalTriadIncidence) →
      alpha ≢ beta →
      pairToSample alpha beta ∈ Preferred.samples preferred) where

  system = Field30.finiteSystem physicalSystem
  cutoff = Audit.cutoff system

  module O = R540.LiteralOrdered physicalSystem S

  items = Output.physicalOutputFiber cutoff output

  physicalCorrespondence :
    Compiler.OrderedOffDiagonalR571Correspondence
      Physical.PhysicalTriadIncidence
  physicalCorrespondence = record
    { Compiler.pairScalar = O.Swap.symmetricWeightedRemainder
    ; Compiler.pairToSample = pairToSample
    ; Compiler.preferredBudget = preferred
    ; Compiler.pairBelowPairedMagnitude =
        literalPairBelowPairedMagnitude
    ; Compiler.preferredPointwise =
        λ alpha beta distinct →
          Preferred.preferredPointwiseSecondMomentBound
            preferred
            (pairToSample alpha beta)
            (sampleInPreferredFamily alpha beta distinct)
    }

  physicalOutputFibreOrderedOffDiagonalBelowM2 :
    R539.orderedOffDiagonalSum
      O.Swap.symmetricWeightedRemainder
      items
    ≤
    Compiler.orderedOffDiagonalM2
      physicalCorrespondence
      items
  physicalOutputFibreOrderedOffDiagonalBelowM2 =
    Compiler.orderedOffDiagonalBelowM2
      physicalCorrespondence
      items
      (Unique.physicalOutputFiberUnique cutoff output)

  twoLiteralR396RemainderBelowM2 :
    (positive : O.E.PairRatePositiveOn items) →
    R539.two *
      R385.sumWeightedRemainder
        (O.E.allR290Pairs items positive)
    ≤
    Compiler.orderedOffDiagonalM2
      physicalCorrespondence
      items
  twoLiteralR396RemainderBelowM2 positive =
    subst
      (λ lower →
        lower ≤
          Compiler.orderedOffDiagonalM2
            physicalCorrespondence
            items)
      (O.orderedOffDiagonalIsTwoLiteralWeightedRemainder
        items positive)
      physicalOutputFibreOrderedOffDiagonalBelowM2

------------------------------------------------------------------------
-- Machine-readable frontier.
------------------------------------------------------------------------

physicalR540CarrierInstantiated : Bool
physicalR540CarrierInstantiated = true

physicalOutputFibreUniquenessDischarged : Bool
physicalOutputFibreUniquenessDischarged = true

literalR396RemainderLandsInPreferredM2GivenPairRealization : Bool
literalR396RemainderLandsInPreferredM2GivenPairRealization = true

physicalPairToR571SampleSameObjectConstructedHere : Bool
physicalPairToR571SampleSameObjectConstructedHere = false

physicalPreferredEnvelopeConstructedHere : Bool
physicalPreferredEnvelopeConstructedHere = false

clayPromotion : Bool
clayPromotion = false

physicalR540CarrierInstantiatedIsTrue :
  physicalR540CarrierInstantiated ≡ true
physicalR540CarrierInstantiatedIsTrue = refl

physicalOutputFibreUniquenessDischargedIsTrue :
  physicalOutputFibreUniquenessDischarged ≡ true
physicalOutputFibreUniquenessDischargedIsTrue = refl

literalR396RemainderLandsInPreferredM2GivenPairRealizationIsTrue :
  literalR396RemainderLandsInPreferredM2GivenPairRealization ≡ true
literalR396RemainderLandsInPreferredM2GivenPairRealizationIsTrue = refl
