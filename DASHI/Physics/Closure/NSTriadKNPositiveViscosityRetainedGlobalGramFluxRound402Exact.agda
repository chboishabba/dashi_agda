module DASHI.Physics.Closure.NSTriadKNPositiveViscosityRetainedGlobalGramFluxRound402Exact where

------------------------------------------------------------------------
-- ROUND402 / POSITIVE VISCOSITY + RETAINED NONZERO MODES -> GLOBAL R378 FLUX
--
-- R398 aggregates one local positivity witness for every output selected in a
-- finite output list.  A PhysicalFiniteComplex3GalerkinSystem already proves
-- every retained mode is nonzero.  R400 constructs the required fibre-local
-- pair-rate positivity from that nonzero output and positive viscosity.
--
-- Therefore, when the R378 global debt is summed over the system's literal
-- retained mode list at the system's literal cutoff, no pair-rate positivity
-- witness remains caller-selected.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (Positive)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNFibreLocalR378GlobalInstantaneousGramFluxRound398Exact as R398
import DASHI.Physics.Closure.NSTriadKNRationalPhysicalPairRatePositivityRound400Exact as R400

F : C3.RealField _
F = Rational.rationalRealField

module RetainedGlobalFlux
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

  system = Field30.finiteSystem physicalSystem
  cutoff = Audit.cutoff system
  outputs = Audit.modes system

  module Global = R398.GlobalFluxLocal physicalSystem S L H P
  module Rate = R400.PhysicalRate physicalSystem S viscosityPositive

  buildOutputPositivity :
    (selected : List Z3.FourierMode) →
    ((mode : Z3.FourierMode) → mode Cube.∈ selected → mode Cube.∈ outputs) →
    Global.OutputFibresPositiveOn cutoff selected
  buildOutputPositivity [] included = Global.positiveOutputsNil
  buildOutputPositivity (output ∷ rest) included =
    Global.positiveOutputsCons
      (Rate.physicalOutputFibrePairRatesPositive
        cutoff output
        (Field30.retainedModeNonzero physicalSystem output
          (included output (Cube.here refl))))
      (buildOutputPositivity rest
        (λ mode member → included mode (Cube.there member)))

  retainedOutputPositivity :
    Global.OutputFibresPositiveOn cutoff outputs
  retainedOutputPositivity =
    buildOutputPositivity outputs (λ mode member → member)

  literalRetainedGlobalGramFluxIdentity =
    Global.literalGlobalGramFluxIdentity
      cutoff outputs retainedOutputPositivity

round402CallerSuppliesAnyR290PairRatePositivity : Bool
round402CallerSuppliesAnyR290PairRatePositivity = false

round402RetainedModeNonzeroProofsFundAllSelectedFibres : Bool
round402RetainedModeNonzeroProofsFundAllSelectedFibres = true

round402LiteralRetainedGlobalR378InstantaneousFluxClosed : Bool
round402LiteralRetainedGlobalR378InstantaneousFluxClosed = true
