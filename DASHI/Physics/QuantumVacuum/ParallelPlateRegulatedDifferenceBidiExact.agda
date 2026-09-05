module DASHI.Physics.QuantumVacuum.ParallelPlateRegulatedDifferenceBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RenormalisedDifferenceLimitExact as RDL
import DASHI.Analysis.SumIntegralDefectExact as SID
import DASHI.Analysis.PoissonSummationKernelBidiExact as PS
import DASHI.Physics.QuantumVacuum.ParallelPlateModeSpectrumCutsetExact as Cutset
import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.PhysicalQuantities as Q

------------------------------------------------------------------------
-- CASIMIR-NATIVE REGULATED DIFFERENCE, BIDI
--
-- This module does not prove the hard analytic limit.  It proves that the
-- Casimir object fits the generic theorem shapes without importing a foreign
-- application instance.
------------------------------------------------------------------------

record CasimirRegulatedDifference
    (kernel : Casimir.CasimirScalarModel) : Set₁ where
  field
    spectrum : Cutset.ParallelPlateSpectralModel kernel
    regulator : Cutset.ParallelPlateRegulator spectrum

    separation : Q.Length

    subtractScalar :
      Casimir.Scalar kernel → Casimir.Scalar kernel → Casimir.Scalar kernel

    regulatedDifference :
      Cutset.Cutoff regulator → Casimir.Scalar kernel

    differenceLaw : (Λ : Cutset.Cutoff regulator) →
      regulatedDifference Λ ≡
      subtractScalar
        (Cutset.regulatedPlateEnergy regulator separation Λ)
        (Cutset.regulatedReferenceEnergy regulator separation Λ)

    reading : String

open CasimirRegulatedDifference public

asGenericDifferenceFamily :
  (kernel : Casimir.CasimirScalarModel) →
  CasimirRegulatedDifference kernel →
  RDL.DifferenceFamily
asGenericDifferenceFamily kernel C = record
  { Regulator = Cutset.Cutoff (regulator C)
  ; Value = Casimir.Scalar kernel
  ; Limit = Casimir.Scalar kernel
  ; left = Cutset.regulatedPlateEnergy (regulator C) (separation C)
  ; right = Cutset.regulatedReferenceEnergy (regulator C) (separation C)
  ; difference = regulatedDifference C
  ; subtract = subtractScalar C
  ; differenceLaw = differenceLaw C
  ; reading = "Casimir-native regulated plate/reference difference."
  }

------------------------------------------------------------------------
-- Reverse obligation projection.
------------------------------------------------------------------------

record CasimirDifferenceObligations
    (kernel : Casimir.CasimirScalarModel)
    (C : CasimirRegulatedDifference kernel) : Set₁ where
  field
    sameCutoffUsedOnBothSides : Set
    sameScalarCarrier : Set
    referenceMatchingPhysical : Set
    regulatedDifferenceConverges : Set

open CasimirDifferenceObligations public

------------------------------------------------------------------------
-- Sum-minus-continuum defect representation.
------------------------------------------------------------------------

record CasimirLongitudinalDefect
    (kernel : Casimir.CasimirScalarModel) : Set₁ where
  field
    Parameter : Set
    Integrand : Set

    discreteLongitudinal : Parameter → Integrand → Casimir.Scalar kernel
    continuumLongitudinal : Parameter → Integrand → Casimir.Scalar kernel
    subtractScalar : Casimir.Scalar kernel → Casimir.Scalar kernel → Casimir.Scalar kernel

    defect : Parameter → Integrand → Casimir.Scalar kernel
    defectLaw : (p : Parameter) → (f : Integrand) →
      defect p f ≡ subtractScalar (discreteLongitudinal p f) (continuumLongitudinal p f)

    reading : String

open CasimirLongitudinalDefect public

asGenericSumIntegralDefect :
  (kernel : Casimir.CasimirScalarModel) →
  CasimirLongitudinalDefect kernel →
  SID.SumIntegralDefect
asGenericSumIntegralDefect kernel D = record
  { Parameter = Parameter D
  ; Function = Integrand D
  ; Value = Casimir.Scalar kernel
  ; discrete = discreteLongitudinal D
  ; continuum = continuumLongitudinal D
  ; subtract = subtractScalar D
  ; defect = defect D
  ; defectLaw = defectLaw D
  ; reading = "Casimir longitudinal discrete-minus-continuum defect."
  }

------------------------------------------------------------------------
-- Optional Poisson producer socket.  The application must construct this
-- problem on the literal Casimir defect integrand and then prove the receipt.
------------------------------------------------------------------------

record CasimirPoissonProducer
    (kernel : Casimir.CasimirScalarModel) : Set₁ where
  field
    problem : PS.PoissonSummationProblem
    sameCasimirDefectObject : Set
    producerReading : String

open CasimirPoissonProducer public

record CasimirPoissonClosure
    (kernel : Casimir.CasimirScalarModel)
    (producer : CasimirPoissonProducer kernel) : Set₁ where
  field
    poissonReceipt : PS.PoissonSummationReceipt (problem producer)
    weldToCasimirDefect : sameCasimirDefectObject producer

open CasimirPoissonClosure public

------------------------------------------------------------------------
-- BIDI authority firewall.
------------------------------------------------------------------------

data ForeignRiemannPoissonClosesCasimirPermission : Set where

data ForeignYangMillsCutoffClosesCasimirPermission : Set where

riemannPoissonCannotAutoCloseCasimir :
  ForeignRiemannPoissonClosesCasimirPermission → ⊥
riemannPoissonCannotAutoCloseCasimir ()

yangMillsCutoffCannotAutoCloseCasimir :
  ForeignYangMillsCutoffClosesCasimirPermission → ⊥
yangMillsCutoffCannotAutoCloseCasimir ()
