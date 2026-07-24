module DASHI.Physics.Closure.NSPeriodicIntegratedExpenditureStandardAdapter where

open import Agda.Primitive using (Level)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSCompactGammaConcretePotentialInstantiation as Potential
import DASHI.Physics.Closure.NSCompactGammaAnalyticLeafCompletion as Leaves
import DASHI.Physics.Closure.NSCompactGammaConcreteBernsteinEnvelopeDomain as Bernstein
import DASHI.Physics.Closure.NSCompactGammaStandardAnalysisCompletion as Standard

------------------------------------------------------------------------
-- Direct adapter for Wall II using the repository's existing concrete real
-- integration and BE1--BE8 Bernstein packages.
--
-- This avoids introducing a second integration theorem.  Once the concrete
-- reserve derivatives and Bernstein leaves are supplied, the weighted-shell and
-- vorticity expenditure bounds follow by the already machine-checked endpoint
-- inequality and transitivity.
------------------------------------------------------------------------

standardIntegratedExpenditureRightHandSide :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t}
    {C : Standard.ConcreteRealIntegrationCompletion A Time} →
  Scalar A
standardIntegratedExpenditureRightHandSide {A = A} {C = C} =
  _+_ A
    (Potential.totalPotential
      (Leaves.reserveLeavesToConcretePotential (Standard.reserveLeaves C))
      (Leaves.initialTime (Standard.reserveLeaves C)))
    (Leaves.forcingAndDataRemainder
      (Standard.realFundamentalTheoremRealization C))

periodicStandardWeightedShellExpenditure :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  (C : Standard.ConcreteRealIntegrationCompletion A Time) →
  (B : Bernstein.ConcreteBernsteinEnvelopeLeaves
    A
    (Standard.calculus C)
    (Standard.reserveLeaves C)
    (Standard.realFundamentalTheoremRealization C)) →
  _≤_ A
    (Bernstein.weightedShellIntegral B)
    (standardIntegratedExpenditureRightHandSide {C = C})
periodicStandardWeightedShellExpenditure {A = A} C B =
  ≤-trans A
    (Bernstein.BE7-weighted-shell-below-coercive-envelope B)
    (Standard.endpointExpenditureInequality C)

periodicStandardVorticityExpenditure :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  (C : Standard.ConcreteRealIntegrationCompletion A Time) →
  (B : Bernstein.ConcreteBernsteinEnvelopeLeaves
    A
    (Standard.calculus C)
    (Standard.reserveLeaves C)
    (Standard.realFundamentalTheoremRealization C)) →
  _≤_ A
    (Bernstein.vorticityIntegral B)
    (standardIntegratedExpenditureRightHandSide {C = C})
periodicStandardVorticityExpenditure {A = A} C B =
  ≤-trans A
    (Bernstein.BE4-integrated-vorticity-reconstruction B)
    (periodicStandardWeightedShellExpenditure C B)

record StandardBKMContinuationFromExpenditure
    {t : Level}
    (A : AbsorptionArithmetic)
    {Time : Set t}
    (C : Standard.ConcreteRealIntegrationCompletion A Time)
    (B : Bernstein.ConcreteBernsteinEnvelopeLeaves
      A
      (Standard.calculus C)
      (Standard.reserveLeaves C)
      (Standard.realFundamentalTheoremRealization C)) : Set t where
  field
    VorticityExpenditureFinite : Set t
    vorticityBoundImpliesFinite :
      _≤_ A
        (Bernstein.vorticityIntegral B)
        (standardIntegratedExpenditureRightHandSide {C = C}) →
      VorticityExpenditureFinite

    Continuation : Set t
    bkmContinuation : VorticityExpenditureFinite → Continuation

open StandardBKMContinuationFromExpenditure public

periodicStandardBKMContinuation :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t}
    {C : Standard.ConcreteRealIntegrationCompletion A Time}
    {B : Bernstein.ConcreteBernsteinEnvelopeLeaves
      A
      (Standard.calculus C)
      (Standard.reserveLeaves C)
      (Standard.realFundamentalTheoremRealization C)} →
  (K : StandardBKMContinuationFromExpenditure A C B) →
  Continuation K
periodicStandardBKMContinuation {C = C} {B = B} K =
  bkmContinuation K
    (vorticityBoundImpliesFinite K
      (periodicStandardVorticityExpenditure C B))
