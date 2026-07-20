module DASHI.Unified.ThreadCompletionFrontier where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.HyperrealUltrapowerConstruction as Hyperreal
import DASHI.Applications.ThreadEmpiricalValidationProgramme as Empirical
import DASHI.Dynamics.ConcreteCoalitionPopulationDynamics as Population
import DASHI.Foundations.OperationalQ3GeometricSeries as Q3
import DASHI.Foundations.PrimorialFactorAddressConcrete as Primorial
import DASHI.Geometry.CalabiYauAnalysisAndPhysicalUseBoundary as Calabi
import DASHI.Sheaf.FiniteTemporalClopenSheaf as Sheaf
import DASHI.Topology.FiniteBraidRhizomeCalculus as Braid

------------------------------------------------------------------------
-- Exact regression witnesses.

finiteSheafGlueRegression :
  Sheaf.restrictU
    (Data.Product.proj₁
      (Sheaf.glue
        (Sheaf.compatible
          Sheaf.absent
          Sheaf.present
          Sheaf.absent)))
  ≡ Sheaf.leftSection Sheaf.absent Sheaf.present
finiteSheafGlueRegression = refl

braidSwapSquaredRegression :
  Braid.compose Braid.swap Braid.swap ≡ Braid.straight
braidSwapSquaredRegression = refl

principalSequenceAdditionRegression :
  Hyperreal.pointwiseAdd
    (Hyperreal.constant 1)
    (Hyperreal.constant 2)
    0
  ≡ 3
principalSequenceAdditionRegression = refl

q3PartialDepth3Regression :
  Q3.geometricPartial 3 ≡ Data.Rational._/_ (Data.Integer.+ 13) 1
q3PartialDepth3Regression = Q3.precision3

populationSelectionRegression :
  Population.select Population.AA ≡ Population.AB
populationSelectionRegression = refl

primorial24Regression :
  Primorial.primeExponentProduct4 Primorial.example24Digits ≡ 625
primorial24Regression = Primorial.example24Product

------------------------------------------------------------------------
-- Aggregate receipt.

record ThreadCompletionFrontierReceipt : Set₃ where
  field
    finiteTemporalSheaf : Sheaf.FiniteTemporalClopenSheafReceipt
    finiteBraidRhizome : Braid.FiniteBraidRhizomeReceipt
    hyperrealBoundary : Hyperreal.HyperrealConstructionBoundary
    q3Boundary : Q3.OperationalQ3GeometricSeriesBoundary
    populationBoundary : Population.CoalitionPopulationReceipt
    primorialBoundary : Primorial.PrimorialFactorAddressConcreteReceipt
    calabiBoundary : Calabi.CalabiYauAnalysisPhysicalBoundary
    empiricalBoundary : Empirical.ThreadEmpiricalValidationBoundary

threadCompletionFrontierReceipt : ThreadCompletionFrontierReceipt
threadCompletionFrontierReceipt =
  record
    { finiteTemporalSheaf = Sheaf.finiteTemporalClopenSheafReceipt
    ; finiteBraidRhizome = Braid.finiteBraidRhizomeReceipt
    ; hyperrealBoundary = Hyperreal.canonicalHyperrealConstructionBoundary
    ; q3Boundary = Q3.canonicalOperationalQ3GeometricSeriesBoundary
    ; populationBoundary = Population.coalitionPopulationReceipt
    ; primorialBoundary = Primorial.primorialFactorAddressConcreteReceipt
    ; calabiBoundary = Calabi.canonicalCalabiYauAnalysisPhysicalBoundary
    ; empiricalBoundary = Empirical.canonicalThreadEmpiricalValidationBoundary
    }
