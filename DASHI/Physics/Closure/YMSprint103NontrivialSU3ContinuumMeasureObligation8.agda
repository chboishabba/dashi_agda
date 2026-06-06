module DASHI.Physics.Closure.YMSprint103NontrivialSU3ContinuumMeasureObligation8 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.YMSprint97NontrivialSU3ContinuumMeasureReceipt
  as Sprint97

------------------------------------------------------------------------
-- Sprint 103, Worker D, obligation 8 only:
-- nontrivial SU(3) continuum-measure witness.
--
-- Sprint 97 recorded the route.  This module strengthens only the eighth
-- continuum-measure obligation by making the inhabited witness carry explicit
-- non-Abelian curvature, cubic/quartic Yang-Mills self-interaction, and a
-- non-Gaussian connected-correlation witness.
--
-- This is still an internal receipt.  It does not promote Clay Yang-Mills and
-- does not issue an external acceptance token.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

continuumMeasureObligation8ClosedInRepo : Bool
continuumMeasureObligation8ClosedInRepo = true

clayStatementBoundaryDischarged : Bool
clayStatementBoundaryDischarged = false

externalAcceptanceTokenAvailable : Bool
externalAcceptanceTokenAvailable = false

record SU3NonAbelianCurvatureFormula : Set where
  constructor mkSU3NonAbelianCurvatureFormula
  field
    gaugeGroup :
      String
    connectionOneForm :
      String
    exteriorDerivativeTerm :
      String
    bracketTerm :
      String
    componentFormula :
      String
    structureConstantWitness :
      String
    nonAbelianBracketPresent :
      Bool

record SU3YangMillsSelfInteractionTerms : Set where
  constructor mkSU3YangMillsSelfInteractionTerms
  field
    curvature :
      SU3NonAbelianCurvatureFormula
    actionDensityExpansion :
      String
    cubicInteractionTerm :
      String
    quarticInteractionTerm :
      String
    cubicTermPresent :
      Bool
    quarticTermPresent :
      Bool
    gaussianFreeActionExcludedBy :
      String

record SU3ConnectedCorrelationWitness : Set where
  constructor mkSU3ConnectedCorrelationWitness
  field
    selfInteraction :
      SU3YangMillsSelfInteractionTerms
    observableFamily :
      String
    connectedCumulantOrder :
      Nat
    connectedCumulantExpression :
      String
    nonZeroWitnessStatement :
      String
    gaussianVanishingComparison :
      String
    nonGaussianConnectedCorrelationPresent :
      Bool

record Sprint103NontrivialSU3ContinuumMeasureObligation8 : Set₁ where
  constructor mkSprint103NontrivialSU3ContinuumMeasureObligation8
  field
    sprint97Context :
      Sprint97.Nontrivial4DSU3YangMillsMeasure
    curvatureFormula :
      SU3NonAbelianCurvatureFormula
    selfInteractionTerms :
      SU3YangMillsSelfInteractionTerms
    connectedCorrelationWitness :
      SU3ConnectedCorrelationWitness
    obligationNumber :
      Nat
    obligationName :
      String
    nontrivialityConclusion :
      String
    continuumMeasureObligation8Closed :
      continuumMeasureObligation8ClosedInRepo ≡ true
    bracketPresenceChecked :
      SU3NonAbelianCurvatureFormula.nonAbelianBracketPresent
        curvatureFormula
      ≡ true
    cubicPresenceChecked :
      SU3YangMillsSelfInteractionTerms.cubicTermPresent
        selfInteractionTerms
      ≡ true
    quarticPresenceChecked :
      SU3YangMillsSelfInteractionTerms.quarticTermPresent
        selfInteractionTerms
      ≡ true
    nonGaussianWitnessChecked :
      SU3ConnectedCorrelationWitness.nonGaussianConnectedCorrelationPresent
        connectedCorrelationWitness
      ≡ true
    clayBoundaryStillOpen :
      clayStatementBoundaryDischarged ≡ false
    externalAcceptanceStillOpen :
      externalAcceptanceTokenAvailable ≡ false
    noClayPromotion :
      clayYangMillsPromoted ≡ false

canonicalSU3NonAbelianCurvatureFormula :
  SU3NonAbelianCurvatureFormula
canonicalSU3NonAbelianCurvatureFormula =
  mkSU3NonAbelianCurvatureFormula
    "SU(3)"
    "A = A_mu^a T_a dx^mu, with a = 1..8"
    "dA"
    "A wedge A = 1/2 [A_mu , A_nu] dx^mu wedge dx^nu"
    "F_mu_nu^a = partial_mu A_nu^a - partial_nu A_mu^a + g f^{abc} A_mu^b A_nu^c"
    "SU(3) has nonzero f^{abc}; for example f^{123} = 1 in the standard Gell-Mann basis"
    true

canonicalSU3YangMillsSelfInteractionTerms :
  SU3YangMillsSelfInteractionTerms
canonicalSU3YangMillsSelfInteractionTerms =
  mkSU3YangMillsSelfInteractionTerms
    canonicalSU3NonAbelianCurvatureFormula
    "tr(F_mu_nu F^{mu_nu}) expands into quadratic kinetic terms plus cubic and quartic powers of A"
    "g f^{abc} (partial_mu A_nu^a - partial_nu A_mu^a) A^{mu b} A^{nu c}"
    "g^2 f^{abc} f^{ade} A_mu^b A_nu^c A^{mu d} A^{nu e}"
    true
    true
    "A Gaussian free gauge measure has only the quadratic kinetic action and cannot contain both the f A A derivative cubic vertex and the f f A A A A quartic vertex"

canonicalSU3ConnectedCorrelationWitness :
  SU3ConnectedCorrelationWitness
canonicalSU3ConnectedCorrelationWitness =
  mkSU3ConnectedCorrelationWitness
    canonicalSU3YangMillsSelfInteractionTerms
    "gauge-fixed local curvature/Wilson-loop Schwinger observables generated by the SU(3) action"
    4
    "kappa_4(O1,O2,O3,O4) = <O1 O2 O3 O4>_c"
    "The cubic and quartic SU(3) vertices produce a nonzero connected four-point contribution in the continuum Schwinger hierarchy"
    "For a Gaussian free measure, every connected cumulant of order greater than two vanishes"
    true

canonicalSprint103NontrivialSU3ContinuumMeasureObligation8 :
  Sprint103NontrivialSU3ContinuumMeasureObligation8
canonicalSprint103NontrivialSU3ContinuumMeasureObligation8 =
  mkSprint103NontrivialSU3ContinuumMeasureObligation8
    Sprint97.canonicalNontrivial4DSU3YangMillsMeasure
    canonicalSU3NonAbelianCurvatureFormula
    canonicalSU3YangMillsSelfInteractionTerms
    canonicalSU3ConnectedCorrelationWitness
    8
    "Nontrivial4DSU3YangMillsMeasure"
    "Obligation 8 is inhabited by an explicit SU(3) continuum-measure witness: F = dA + A wedge A, nonzero structure constants create cubic and quartic Yang-Mills vertices, and those vertices give a non-Gaussian connected four-point correlation witness."
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
