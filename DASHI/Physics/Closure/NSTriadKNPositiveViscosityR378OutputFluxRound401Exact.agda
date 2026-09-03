module DASHI.Physics.Closure.NSTriadKNPositiveViscosityR378OutputFluxRound401Exact where

------------------------------------------------------------------------
-- ROUND401 / POSITIVE VISCOSITY -> LITERAL NONZERO-OUTPUT R378 FLUX
--
-- R397's only remaining algebraic caller input was a fibre-local R290 pair-rate
-- positivity witness.  R400 now constructs exactly that witness from positive
-- viscosity and a nonzero output.  Therefore the one-output instantaneous
-- R378 -> R290 flux identity has no caller-supplied reciprocal/positivity data.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using (Positive)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNFibreLocalR378InstantaneousGramFluxRound397Exact as R397
import DASHI.Physics.Closure.NSTriadKNRationalPhysicalPairRatePositivityRound400Exact as R400

F : C3.RealField _
F = Rational.rationalRealField

module PositiveViscosityOutputFlux
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
    (viscosityPositive : Positive (Field30.viscosity physicalSystem)) where

  module Flux = R397.LiteralOutputFluxLocal physicalSystem S L H P
  module Rate = R400.PhysicalRate physicalSystem S viscosityPositive

  literalNonzeroOutputGramFluxIdentity =
    λ (cutoff : Nat) (output : Z3.FourierMode)
      (outputNonzero : Z3.NonZeroMode output) →
      Flux.literalOutputGramFluxIdentity cutoff output
        (Rate.physicalOutputFibrePairRatesPositive
          cutoff output outputNonzero)

round401CallerSuppliesPairRatePositivity : Bool
round401CallerSuppliesPairRatePositivity = false

round401PositiveViscosityAndNonzeroOutputReachR290Flux : Bool
round401PositiveViscosityAndNonzeroOutputReachR290Flux = true
