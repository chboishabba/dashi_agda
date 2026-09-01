module DASHI.Physics.Closure.NSTriadKNLiteralR378InstantaneousGramFluxRound391Exact where

------------------------------------------------------------------------
-- ROUND391 / LITERAL R378 DEBT -> INSTANTANEOUS R290 FLUX IDENTITY
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using (Positive)
open import Data.Rational.Base using (0ℚ; _+_; _-_)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNPhysicalGlobalCompanionGramLedgerRound378Exact as R378
import DASHI.Physics.Closure.NSTriadKNCompanionDebtDoubleMixedCarrierRound386Exact as R386
import DASHI.Physics.Closure.NSTriadKNDoubleMixedGramPairToResolventRound389Exact as R389
import DASHI.Physics.Closure.NSTriadKNLiteralGramDebtR290PairEnumerationRound390Exact as R390
import DASHI.Physics.Closure.NSTriadKNFiniteWeightedGramFluxAggregationRound385Exact as R385

F : C3.RealField _
F = Rational.rationalRealField

module LiteralOutputFlux
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (P : R225.PhysicalFixedOutputHelicityData
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem)
      S L H
      (Audit.velocityAt (Field30.finiteSystem physicalSystem)))
    (positivePairRate :
      (alpha beta : Physical.PhysicalTriadIncidence) →
      Positive
        (R291.pairRate
          (R389.DoubleMixedPair.physicalDoubleMixedPair
            physicalSystem S alpha beta))) where

  E = Field30.physicalEmbedding physicalSystem
  velocity = Audit.velocityAt (Field30.finiteSystem physicalSystem)

  module Carrier = R386.OutputCarrier E
    (Field30.physicalInverseSquare physicalSystem) S L H velocity P
  module Pairs = R390.Enumerate physicalSystem S positivePairRate

  outputPairs : Nat → Z3.FourierMode → List R290.DampedGramPair
  outputPairs cutoff output =
    Pairs.allR290Pairs (Output.physicalOutputFiber cutoff output)

  literalOutputGramFluxIdentity :
    (cutoff : Nat) (output : Z3.FourierMode) →
    R378.outputGramDebt E S velocity cutoff output
    ≡
    (0ℚ - R385.sumWeightedFluxTangent (outputPairs cutoff output))
      + R385.sumWeightedRemainder (outputPairs cutoff output)
  literalOutputGramFluxIdentity cutoff output =
    let fibre = Output.physicalOutputFiber cutoff output in
    trans
      (Carrier.outputGramDebtIsDoubleMixedDebt cutoff output)
      (trans
        (Pairs.r180DebtIsR290PairGramSum fibre)
        (R385.finiteGramAsNegativeFluxDerivativePlusRemainder
          (Pairs.allR290Pairs fibre)))

round391LiteralR378InstantaneousGramFluxClosed : Bool
round391LiteralR378InstantaneousGramFluxClosed = true

round391SameObjectTemporalDerivativeIntegrated : Bool
round391SameObjectTemporalDerivativeIntegrated = false

round391EndpointFundamentalTheoremApplied : Bool
round391EndpointFundamentalTheoremApplied = false

round391LiteralR378InstantaneousGramFluxClosedIsTrue :
  round391LiteralR378InstantaneousGramFluxClosed ≡ true
round391LiteralR378InstantaneousGramFluxClosedIsTrue = refl
