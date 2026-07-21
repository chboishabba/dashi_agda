module DASHI.Physics.Closure.NSCompactGammaStandardAnalysisCompletion where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSCompactGammaConcretePotentialInstantiation as Potential
import DASHI.Physics.Closure.NSCompactGammaAnalyticLeafCompletion as Leaves
import DASHI.Physics.Closure.NSCompactGammaRealAnalysisGalerkinCompletion as Real
import DASHI.Physics.Closure.NSConcreteAubinLionsNonlinearLimitWitnesses as Galerkin
import DASHI.Physics.Closure.NSCompactGammaReserveDifferentialIdentities as Reserve
import DASHI.Physics.Closure.NSCompactGammaConcreteBernsteinEnvelopeDomain as Bernstein

------------------------------------------------------------------------
-- RI1--RI9: selected real integration completion.
------------------------------------------------------------------------

record ConcreteRealIntegrationCompletion
    {t : Level}
    (A : AbsorptionArithmetic)
    (Time : Set t) : Set (lsuc t) where
  field
    calculus : Potential.ThreeWayAdditiveCalculus A
    reserveLeaves : Leaves.ConcreteReserveLeaves A Time
    realAnalysis : Real.AbsolutelyContinuousRealAnalysis A Time
    fundamentalLeaves :
      Real.RealFundamentalTheoremLeaves
        A calculus reserveLeaves realAnalysis

    Measurable : (Time → Scalar A) → Set
    AlmostEverywhereLessEqual :
      (Time → Scalar A) → (Time → Scalar A) → Set

    reservePotentialMeasurable :
      Measurable
        (Potential.totalPotential
          (Leaves.reserveLeavesToConcretePotential reserveLeaves))

    coerciveRateMeasurable :
      Measurable
        (Potential.totalCoerciveRate
          (Leaves.reserveLeavesToConcretePotential reserveLeaves))

    forcingRateMeasurable :
      Measurable
        (Potential.totalForcingRate
          (Leaves.reserveLeavesToConcretePotential reserveLeaves))

    pointwiseInequalityAlmostEverywhere :
      AlmostEverywhereLessEqual
        (λ τ →
          _+_ A
            (Potential.totalPotentialDerivative
              (Leaves.reserveLeavesToConcretePotential reserveLeaves) τ)
            (Potential.totalCoerciveRate
              (Leaves.reserveLeavesToConcretePotential reserveLeaves) τ))
        (λ τ →
          _+_ A
            (Potential.totalDissipationRate
              (Leaves.reserveLeavesToConcretePotential reserveLeaves) τ)
            (Potential.totalForcingRate
              (Leaves.reserveLeavesToConcretePotential reserveLeaves) τ))

    integralMonotonicity :
      ∀ {f g} →
      Measurable f → Measurable g →
      AlmostEverywhereLessEqual f g →
      _≤_ A
        (Real.Integral realAnalysis f)
        (Real.Integral realAnalysis g)

    endpointExpenditureInequality :
      _≤_ A
        (Real.Integral realAnalysis
          (Potential.totalCoerciveRate
            (Leaves.reserveLeavesToConcretePotential reserveLeaves)))
        (_+_ A
          (Potential.totalPotential
            (Leaves.reserveLeavesToConcretePotential reserveLeaves)
            (Leaves.initialTime reserveLeaves))
          (_+_ A
            (Real.Integral realAnalysis
              (Potential.totalForcingRate
                (Leaves.reserveLeavesToConcretePotential reserveLeaves)))
            (Real.dataRemainder fundamentalLeaves)))

open ConcreteRealIntegrationCompletion public

reservePotentialAbsolutelyContinuous :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  (C : ConcreteRealIntegrationCompletion A Time) →
  Real.AbsolutelyContinuous (realAnalysis C)
    (Potential.totalPotential
      (Leaves.reserveLeavesToConcretePotential (reserveLeaves C)))
reservePotentialAbsolutelyContinuous C =
  Real.potentialAbsolutelyContinuous (fundamentalLeaves C)

coerciveRateIntegrable :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  (C : ConcreteRealIntegrationCompletion A Time) →
  Real.Integrable (realAnalysis C)
    (Potential.totalCoerciveRate
      (Leaves.reserveLeavesToConcretePotential (reserveLeaves C)))
coerciveRateIntegrable C =
  Real.coerciveRateIntegrable (fundamentalLeaves C)

forcingRateIntegrable :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  (C : ConcreteRealIntegrationCompletion A Time) →
  Real.Integrable (realAnalysis C)
    (Potential.totalForcingRate
      (Leaves.reserveLeavesToConcretePotential (reserveLeaves C)))
forcingRateIntegrable C =
  Real.forcingRateIntegrable (fundamentalLeaves C)

fundamentalTheoremForReservePotential :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  (C : ConcreteRealIntegrationCompletion A Time) →
  _+_ A
    (Potential.totalPotential
      (Leaves.reserveLeavesToConcretePotential (reserveLeaves C))
      (Leaves.initialTime (reserveLeaves C)))
    (Real.Integral (realAnalysis C)
      (Potential.totalDissipationRate
        (Leaves.reserveLeavesToConcretePotential (reserveLeaves C))))
  ≡
  _+_ A
    (Potential.totalPotential
      (Leaves.reserveLeavesToConcretePotential (reserveLeaves C))
      (Leaves.finalTime (reserveLeaves C)))
    (Real.Integral (realAnalysis C)
      (Potential.totalCoerciveRate
        (Leaves.reserveLeavesToConcretePotential (reserveLeaves C))))
fundamentalTheoremForReservePotential C =
  Real.integratedPointwiseIdentity (fundamentalLeaves C)

integralAddition :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  (C : ConcreteRealIntegrationCompletion A Time) →
  ∀ {f g} →
  Real.Integrable (realAnalysis C) f →
  Real.Integrable (realAnalysis C) g →
  Real.Integral (realAnalysis C) (λ τ → _+_ A (f τ) (g τ)) ≡
  _+_ A (Real.Integral (realAnalysis C) f)
         (Real.Integral (realAnalysis C) g)
integralAddition C = Real.integralAdditive (realAnalysis C)

realFundamentalTheoremRealization :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  (C : ConcreteRealIntegrationCompletion A Time) →
  Leaves.RealFundamentalTheoremRealization
    A (calculus C) (reserveLeaves C)
realFundamentalTheoremRealization C =
  Real.realLeavesToFundamentalTheoremRealization
    (calculus C) (reserveLeaves C) (realAnalysis C) (fundamentalLeaves C)

------------------------------------------------------------------------
-- GE/G1--G19: exact Galerkin and Aubin--Lions projections.
------------------------------------------------------------------------

galerkinEnergyEquality :
  ∀ {ℓState ℓProp}
    {S : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : Galerkin.ConcreteAubinLionsNonlinearLimitCertificate S) →
  ∀ N → Galerkin.ExactEnergyIdentity S N
galerkinEnergyEquality C = Galerkin.exactIdentity (Galerkin.g2 C)

uniformGalerkinEnergyBound :
  ∀ {ℓState ℓProp}
    {S : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : Galerkin.ConcreteAubinLionsNonlinearLimitCertificate S) →
  Galerkin.UniformEnergyEstimate (Galerkin.analytic S)
uniformGalerkinEnergyBound C =
  Galerkin.uniformEnergyEstimate (Galerkin.g2 C)

uniformGalerkinTimeDerivativeBound :
  ∀ {ℓState ℓProp}
    {S : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : Galerkin.ConcreteAubinLionsNonlinearLimitCertificate S) →
  Galerkin.UniformTimeDerivativeBound (Galerkin.analytic S)
uniformGalerkinTimeDerivativeBound C =
  Galerkin.repositoryBound (Galerkin.g4 C)

aubinLionsStrongL2Extraction :
  ∀ {ℓState ℓProp}
    {S : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : Galerkin.ConcreteAubinLionsNonlinearLimitCertificate S) →
  Galerkin.StrongL2TimeSpaceConvergence
    (Galerkin.analytic S)
    (Galerkin.subsequence (Galerkin.g5 C))
    (Galerkin.LimitState (Galerkin.analytic S))
aubinLionsStrongL2Extraction C =
  Galerkin.repositoryStrongL2 (Galerkin.g5 C)

galerkinNonlinearityConverges :
  ∀ {ℓState ℓProp}
    {S : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : Galerkin.ConcreteAubinLionsNonlinearLimitCertificate S) →
  Galerkin.NonlinearDistributionalConvergence
    (Galerkin.analytic S)
    (Galerkin.subsequence (Galerkin.g5 C))
    (Galerkin.LimitNonlinearity (Galerkin.analytic S))
galerkinNonlinearityConverges C =
  Galerkin.convectionDistribution (Galerkin.g9 C)

limitSolvesNavierStokes :
  ∀ {ℓState ℓProp}
    {S : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : Galerkin.ConcreteAubinLionsNonlinearLimitCertificate S) →
  Galerkin.LerayHopfSolution
    (Galerkin.analytic S)
    (Galerkin.solution (Galerkin.g12 C))
limitSolvesNavierStokes C =
  Galerkin.repositoryLerayHopf (Galerkin.g12 C)

lowerSemicontinuityOfDissipation :
  ∀ {ℓState ℓProp}
    {S : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : Galerkin.ConcreteAubinLionsNonlinearLimitCertificate S) →
  Galerkin.DissipationLowerSemicontinuity
    (Galerkin.analytic S)
    (Galerkin.subsequence (Galerkin.g5 C))
lowerSemicontinuityOfDissipation C =
  Galerkin.repositoryLiminf (Galerkin.g11 C)

record CompactGammaFunctionalConvergencePair
    {ℓState ℓProp}
    {S : Galerkin.ConcreteGalerkinSetting ℓState ℓProp}
    (C : Galerkin.ConcreteAubinLionsNonlinearLimitCertificate S)
    : Set (ℓState ⊔ ℓProp) where
  field
    numerator :
      Galerkin.GammaNumeratorConvergence
        (Galerkin.analytic S)
        (Galerkin.subsequence (Galerkin.g5 C))
    differentiatedNumerator :
      Galerkin.GammaTangentResponseConvergence
        (Galerkin.analytic S)
        (Galerkin.subsequence (Galerkin.g5 C))

open CompactGammaFunctionalConvergencePair public

compactGammaFunctionalsConverge :
  ∀ {ℓState ℓProp}
    {S : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : Galerkin.ConcreteAubinLionsNonlinearLimitCertificate S) →
  CompactGammaFunctionalConvergencePair C
compactGammaFunctionalsConverge C = record
  { numerator = Galerkin.repositoryNumerator (Galerkin.g13 C)
  ; differentiatedNumerator =
      Galerkin.repositoryTangentResponse (Galerkin.g14 C)
  }

differentialInequalityPassesToLimit :
  ∀ {ℓState ℓProp}
    {S : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : Galerkin.ConcreteAubinLionsNonlinearLimitCertificate S) →
  Galerkin.CutoffEstimatePasses
    S
    (Galerkin.subsequence (Galerkin.g5 C))
    (Galerkin.shell (Galerkin.g13 C))
differentialInequalityPassesToLimit C =
  Galerkin.cutoffToLimit (Galerkin.g18 C)

weakStrongUniquenessIdentifiesSelectedPath :
  ∀ {ℓState ℓProp}
    {S : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : Galerkin.ConcreteAubinLionsNonlinearLimitCertificate S) →
  Galerkin.SelectedPathIdentified S
weakStrongUniquenessIdentifiesSelectedPath C =
  Galerkin.selectedPath (Galerkin.g19 C)

------------------------------------------------------------------------
-- OP1--OP7: additional inequality-producing bounds tied to the existing exact
-- off-packet differential data.
------------------------------------------------------------------------

record OffPacketAnalyticCompletion
    {t : Level}
    (A : AbsorptionArithmetic)
    (Time : Set t) : Set (lsuc t) where
  field
    dataSet : Reserve.OffPacketDifferentialData A Time

    remoteShellViscousDamping : ∀ τ →
      _≤_ A
        (Reserve.remoteViscousDamping dataSet τ)
        (Reserve.offPacketCoerciveEnvelope dataSet τ)

    offPacketNearInteractionBound : ∀ τ →
      _≤_ A
        (Reserve.nearShellSchurControl dataSet τ)
        (Reserve.offPacketCoerciveEnvelope dataSet τ)

    offPacketFarTailBound : ∀ τ →
      _≤_ A
        (Reserve.farTailGeometricControl dataSet τ)
        (Reserve.offPacketCoerciveEnvelope dataSet τ)

    offPacketBarrierDerivative : ∀ τ →
      Reserve.offPacketReserveDerivative dataSet τ ≡
      Reserve.selectedOffPacketFunctionalDerivative dataSet τ

    offPacketInwardPointingEstimate : ∀ τ →
      _+_ A
        (Reserve.selectedOffPacketFunctionalDerivative dataSet τ)
        (Reserve.offPacketCoerciveEnvelope dataSet τ)
      ≡
      _+_ A
        (Reserve.offPacketDissipationRate dataSet τ)
        (Reserve.offPacketForcingRate dataSet τ)

open OffPacketAnalyticCompletion public

internalShellTransfersCancel :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  (C : OffPacketAnalyticCompletion A Time) → ∀ τ →
  Reserve.shellTransferSum (dataSet C) τ ≡
  Reserve.boundaryFlux (dataSet C) τ
internalShellTransfersCancel C =
  Reserve.internalTransferCancellation (dataSet C)

offPacketBoundaryFluxIdentity :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  (C : OffPacketAnalyticCompletion A Time) → ∀ τ →
  Reserve.nonlinearOffPacketTransfer (dataSet C) τ ≡
  Reserve.boundaryFlux (dataSet C) τ
offPacketBoundaryFluxIdentity C =
  Reserve.offPacketBoundaryFluxIdentity (dataSet C)

------------------------------------------------------------------------
-- BE1--BE8: audit-friendly aliases for the existing concrete Bernstein chain.
------------------------------------------------------------------------

fiveHalvesShellEstimate :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t}
    {C : Potential.ThreeWayAdditiveCalculus A}
    {R : Leaves.ConcreteReserveLeaves A Time}
    {F : Leaves.RealFundamentalTheoremRealization A C R} →
  (B : Bernstein.ConcreteBernsteinEnvelopeLeaves A C R F) → ∀ j τ →
  _≤_ A
    (Bernstein.shellVorticityLInfinity B j (Bernstein.shellState B τ))
    (Bernstein.curlWeightedShell B j (Bernstein.shellState B τ))
fiveHalvesShellEstimate = Bernstein.BE2-shell-Bernstein-five-halves

vorticityLittlewoodPaleyReconstruction :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t}
    {C : Potential.ThreeWayAdditiveCalculus A}
    {R : Leaves.ConcreteReserveLeaves A Time}
    {F : Leaves.RealFundamentalTheoremRealization A C R} →
  (B : Bernstein.ConcreteBernsteinEnvelopeLeaves A C R F) → ∀ τ →
  _≤_ A
    (Bernstein.vorticityLInfinity B (Bernstein.shellState B τ))
    (Bernstein.weightedShellSum B (Bernstein.shellState B τ))
vorticityLittlewoodPaleyReconstruction =
  Bernstein.BE3-vorticity-reconstruction

weightedShellSeriesTonelli :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t}
    {C : Potential.ThreeWayAdditiveCalculus A}
    {R : Leaves.ConcreteReserveLeaves A Time}
    {F : Leaves.RealFundamentalTheoremRealization A C R} →
  (B : Bernstein.ConcreteBernsteinEnvelopeLeaves A C R F) →
  _≤_ A (Bernstein.vorticityIntegral B) (Bernstein.weightedShellIntegral B)
weightedShellSeriesTonelli =
  Bernstein.BE4-integrated-vorticity-reconstruction

uniformGeometricCoefficientSum :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t}
    {C : Potential.ThreeWayAdditiveCalculus A}
    {R : Leaves.ConcreteReserveLeaves A Time}
    {F : Leaves.RealFundamentalTheoremRealization A C R} →
  (B : Bernstein.ConcreteBernsteinEnvelopeLeaves A C R F) → ∀ τ →
  _≤_ A
    (Bernstein.weightedShellSum B (Bernstein.shellState B τ))
    (Bernstein.envelope B (Bernstein.shellState B τ))
uniformGeometricCoefficientSum =
  Bernstein.BE6-uniform-geometric-shell-sum

weightedShellIntegralBelowGammaEnvelope :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t}
    {C : Potential.ThreeWayAdditiveCalculus A}
    {R : Leaves.ConcreteReserveLeaves A Time}
    {F : Leaves.RealFundamentalTheoremRealization A C R} →
  (B : Bernstein.ConcreteBernsteinEnvelopeLeaves A C R F) →
  _≤_ A (Bernstein.weightedShellIntegral B) (Leaves.coerciveIntegral F)
weightedShellIntegralBelowGammaEnvelope =
  Bernstein.BE7-weighted-shell-below-coercive-envelope
