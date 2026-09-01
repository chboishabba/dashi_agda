module DASHI.Physics.Closure.NSTriadKNFibreLocalR378InstantaneousGramFluxRound397Exact where

------------------------------------------------------------------------
-- ROUND397 / LITERAL R378 OUTPUT FLUX WITH ONLY FIBRE-LOCAL POSITIVITY
--
-- Supersedes the unnecessarily global positivity premise of R391.  The R378
-- output debt only enumerates unordered pairs in `physicalOutputFiber N k`.
-- R396 therefore lets this theorem ask for positivity on exactly that list.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.Closure.NSTriadKNFiniteWeightedGramFluxAggregationRound385Exact as R385
import DASHI.Physics.Closure.NSTriadKNPhysicalGlobalCompanionGramLedgerRound378Exact as R378
import DASHI.Physics.Closure.NSTriadKNCompanionDebtDoubleMixedCarrierRound386Exact as R386
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396

F : C3.RealField _
F = Rational.rationalRealField

module LiteralOutputFluxLocal
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
      (Field30.finiteSystem physicalSystem .DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit.FiniteComplex3GalerkinSystem.velocity)) where

  E = Field30.physicalEmbedding physicalSystem
  velocity =
    Field30.finiteSystem physicalSystem
      .DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit.FiniteComplex3GalerkinSystem.velocity

  module Carrier = R386.OutputCarrier E
    (Field30.physicalInverseSquare physicalSystem) S L H velocity P
  module Local = R396.LocalEnumerate physicalSystem S

  outputPairs :
    (cutoff : Nat) (output : Z3.FourierMode) →
    Local.PairRatePositiveOn (Output.physicalOutputFiber cutoff output) →
    List R290.DampedGramPair
  outputPairs cutoff output positive =
    Local.allR290Pairs (Output.physicalOutputFiber cutoff output) positive

  literalOutputGramFluxIdentity :
    (cutoff : Nat) (output : Z3.FourierMode) →
    (positive : Local.PairRatePositiveOn
      (Output.physicalOutputFiber cutoff output)) →
    R378.outputGramDebt E S velocity cutoff output
    ≡
    (0ℚ - R385.sumWeightedFluxTangent
      (outputPairs cutoff output positive))
      + R385.sumWeightedRemainder
        (outputPairs cutoff output positive)
  literalOutputGramFluxIdentity cutoff output positive =
    let
      fibre = Output.physicalOutputFiber cutoff output
    in
    trans
      (Carrier.outputGramDebtIsDoubleMixedDebt cutoff output)
      (trans
        (Local.r180DebtIsLocalR290PairGramSum fibre positive)
        (R385.finiteGramAsNegativeFluxDerivativePlusRemainder
          (Local.allR290Pairs fibre positive)))

round397LiteralOutputFluxUsesOnlyFibreLocalPositivity : Bool
round397LiteralOutputFluxUsesOnlyFibreLocalPositivity = true

round397GlobalIncidencePositivityPremiseRemoved : Bool
round397GlobalIncidencePositivityPremiseRemoved = true
