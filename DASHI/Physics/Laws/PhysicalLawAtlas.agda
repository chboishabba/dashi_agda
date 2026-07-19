module DASHI.Physics.Laws.PhysicalLawAtlas where

open import Agda.Builtin.List using (List; []; _∷_)
open import DASHI.Physics.Laws.PhysicalLawCore

-- Named law families represented by the recovery tower.  The list includes
-- fundamental equations, conservation principles, constitutive/effective laws,
-- statistical laws, and the limit maps connecting regimes.
data CanonicalPhysicalLaw : Set where
  causalIntervalLaw LorentzInvarianceLaw geodesicLaw : CanonicalPhysicalLaw
  newtonMomentumLaw eulerLagrangeLaw hamiltonEquationLaw noetherLaw : CanonicalPhysicalLaw
  schrodingerLaw unitaryEvolutionLaw bornProbabilityLaw diracLaw : CanonicalPhysicalLaw
  microcausalityLaw aqftIsotonyLaw aqftTimeSliceLaw : CanonicalPhysicalLaw
  gaugeCovarianceLaw gaugeBianchiLaw : CanonicalPhysicalLaw
  homogeneousMaxwellLaw inhomogeneousMaxwellLaw chargeConservationLaw lorentzForceLaw : CanonicalPhysicalLaw
  yangMillsEquationLaw covariantCurrentLaw : CanonicalPhysicalLaw
  strongInteractionLaw weakInteractionLaw : CanonicalPhysicalLaw
  einsteinEquationLaw contractedBianchiLaw stressEnergyConservationLaw : CanonicalPhysicalLaw
  newtonianGravityLimitLaw schwarzschildVacuumLaw friedmannLaw gravitationalWaveLaw : CanonicalPhysicalLaw
  zerothThermodynamicLaw firstThermodynamicLaw secondThermodynamicLaw thirdThermodynamicLaw : CanonicalPhysicalLaw
  equationOfStateLaw ensembleLaw thermodynamicLimitLaw : CanonicalPhysicalLaw
  fluctuationDissipationLaw onsagerTransportLaw detailedBalanceLaw : CanonicalPhysicalLaw
  massBalanceLaw momentumBalanceLaw energyBalanceLaw : CanonicalPhysicalLaw
  hookeElasticityLaw fickDiffusionLaw fourierHeatLaw : CanonicalPhysicalLaw
  navierStokesWeakLaw navierStokesRegularityLaw reactionDiffusionLaw : CanonicalPhysicalLaw
  magnetohydrodynamicLaw waveEquationLaw geometricOpticsLimitLaw acousticLimitLaw : CanonicalPhysicalLaw
  standardModelGaugeLaw anomalyCancellationLaw higgsMechanismLaw : CanonicalPhysicalLaw
  yukawaFlavourLaw ckmPmnsLaw gaugeRunningLaw : CanonicalPhysicalLaw
  atomicSpectrumLaw shellRecurrenceLaw molecularAssemblyLaw : CanonicalPhysicalLaw
  dimensionalConsistencyLaw metrologyTraceabilityLaw : CanonicalPhysicalLaw
  renormalisationGroupLaw discreteContinuumLimitLaw quantumClassicalLimitLaw : CanonicalPhysicalLaw
  kineticFluidLimitLaw microscopicThermodynamicLimitLaw : CanonicalPhysicalLaw

lawDomain : CanonicalPhysicalLaw → PhysicalDomain
lawDomain causalIntervalLaw = spacetimeGeometry
lawDomain LorentzInvarianceLaw = spacetimeGeometry
lawDomain geodesicLaw = spacetimeGeometry
lawDomain newtonMomentumLaw = classicalMechanics
lawDomain eulerLagrangeLaw = classicalMechanics
lawDomain hamiltonEquationLaw = classicalMechanics
lawDomain noetherLaw = classicalMechanics
lawDomain schrodingerLaw = quantumMechanics
lawDomain unitaryEvolutionLaw = quantumMechanics
lawDomain bornProbabilityLaw = quantumMechanics
lawDomain diracLaw = quantumFieldTheory
lawDomain microcausalityLaw = quantumFieldTheory
lawDomain aqftIsotonyLaw = quantumFieldTheory
lawDomain aqftTimeSliceLaw = quantumFieldTheory
lawDomain gaugeCovarianceLaw = gaugeInteractions
lawDomain gaugeBianchiLaw = gaugeInteractions
lawDomain homogeneousMaxwellLaw = electromagnetism
lawDomain inhomogeneousMaxwellLaw = electromagnetism
lawDomain chargeConservationLaw = electromagnetism
lawDomain lorentzForceLaw = electromagnetism
lawDomain yangMillsEquationLaw = gaugeInteractions
lawDomain covariantCurrentLaw = gaugeInteractions
lawDomain strongInteractionLaw = nuclearParticlePhysics
lawDomain weakInteractionLaw = nuclearParticlePhysics
lawDomain einsteinEquationLaw = gravitation
lawDomain contractedBianchiLaw = gravitation
lawDomain stressEnergyConservationLaw = gravitation
lawDomain newtonianGravityLimitLaw = gravitation
lawDomain schwarzschildVacuumLaw = gravitation
lawDomain friedmannLaw = cosmology
lawDomain gravitationalWaveLaw = gravitation
lawDomain zerothThermodynamicLaw = thermodynamics
lawDomain firstThermodynamicLaw = thermodynamics
lawDomain secondThermodynamicLaw = thermodynamics
lawDomain thirdThermodynamicLaw = thermodynamics
lawDomain equationOfStateLaw = thermodynamics
lawDomain ensembleLaw = statisticalMechanics
lawDomain thermodynamicLimitLaw = statisticalMechanics
lawDomain fluctuationDissipationLaw = statisticalMechanics
lawDomain onsagerTransportLaw = statisticalMechanics
lawDomain detailedBalanceLaw = statisticalMechanics
lawDomain massBalanceLaw = continuumMechanics
lawDomain momentumBalanceLaw = continuumMechanics
lawDomain energyBalanceLaw = continuumMechanics
lawDomain hookeElasticityLaw = materialPhysics
lawDomain fickDiffusionLaw = materialPhysics
lawDomain fourierHeatLaw = materialPhysics
lawDomain navierStokesWeakLaw = fluidDynamics
lawDomain navierStokesRegularityLaw = fluidDynamics
lawDomain reactionDiffusionLaw = materialPhysics
lawDomain magnetohydrodynamicLaw = plasmaPhysics
lawDomain waveEquationLaw = opticsAcoustics
lawDomain geometricOpticsLimitLaw = opticsAcoustics
lawDomain acousticLimitLaw = opticsAcoustics
lawDomain standardModelGaugeLaw = standardModel
lawDomain anomalyCancellationLaw = standardModel
lawDomain higgsMechanismLaw = standardModel
lawDomain yukawaFlavourLaw = standardModel
lawDomain ckmPmnsLaw = standardModel
lawDomain gaugeRunningLaw = standardModel
lawDomain atomicSpectrumLaw = atomicMolecularPhysics
lawDomain shellRecurrenceLaw = atomicMolecularPhysics
lawDomain molecularAssemblyLaw = atomicMolecularPhysics
lawDomain dimensionalConsistencyLaw = metrology
lawDomain metrologyTraceabilityLaw = metrology
lawDomain renormalisationGroupLaw = effectiveTheory
lawDomain discreteContinuumLimitLaw = effectiveTheory
lawDomain quantumClassicalLimitLaw = effectiveTheory
lawDomain kineticFluidLimitLaw = effectiveTheory
lawDomain microscopicThermodynamicLimitLaw = effectiveTheory

lawKind : CanonicalPhysicalLaw → PhysicalLawKind
lawKind causalIntervalLaw = kinematicLaw
lawKind LorentzInvarianceLaw = symmetryLaw
lawKind geodesicLaw = dynamicalLaw
lawKind newtonMomentumLaw = dynamicalLaw
lawKind eulerLagrangeLaw = dynamicalLaw
lawKind hamiltonEquationLaw = dynamicalLaw
lawKind noetherLaw = conservationLaw
lawKind schrodingerLaw = dynamicalLaw
lawKind unitaryEvolutionLaw = constraintLaw
lawKind bornProbabilityLaw = statisticalLaw
lawKind diracLaw = dynamicalLaw
lawKind microcausalityLaw = constraintLaw
lawKind aqftIsotonyLaw = constraintLaw
lawKind aqftTimeSliceLaw = constraintLaw
lawKind gaugeCovarianceLaw = symmetryLaw
lawKind gaugeBianchiLaw = conservationLaw
lawKind homogeneousMaxwellLaw = conservationLaw
lawKind inhomogeneousMaxwellLaw = dynamicalLaw
lawKind chargeConservationLaw = conservationLaw
lawKind lorentzForceLaw = dynamicalLaw
lawKind yangMillsEquationLaw = dynamicalLaw
lawKind covariantCurrentLaw = conservationLaw
lawKind strongInteractionLaw = dynamicalLaw
lawKind weakInteractionLaw = dynamicalLaw
lawKind einsteinEquationLaw = dynamicalLaw
lawKind contractedBianchiLaw = conservationLaw
lawKind stressEnergyConservationLaw = conservationLaw
lawKind newtonianGravityLimitLaw = limitLaw
lawKind schwarzschildVacuumLaw = effectiveLaw
lawKind friedmannLaw = effectiveLaw
lawKind gravitationalWaveLaw = effectiveLaw
lawKind zerothThermodynamicLaw = constraintLaw
lawKind firstThermodynamicLaw = conservationLaw
lawKind secondThermodynamicLaw = conservationLaw
lawKind thirdThermodynamicLaw = limitLaw
lawKind equationOfStateLaw = constitutiveLaw
lawKind ensembleLaw = statisticalLaw
lawKind thermodynamicLimitLaw = limitLaw
lawKind fluctuationDissipationLaw = statisticalLaw
lawKind onsagerTransportLaw = constitutiveLaw
lawKind detailedBalanceLaw = stochasticLaw
lawKind massBalanceLaw = conservationLaw
lawKind momentumBalanceLaw = conservationLaw
lawKind energyBalanceLaw = conservationLaw
lawKind hookeElasticityLaw = constitutiveLaw
lawKind fickDiffusionLaw = constitutiveLaw
lawKind fourierHeatLaw = constitutiveLaw
lawKind navierStokesWeakLaw = dynamicalLaw
lawKind navierStokesRegularityLaw = constraintLaw
lawKind reactionDiffusionLaw = dynamicalLaw
lawKind magnetohydrodynamicLaw = effectiveLaw
lawKind waveEquationLaw = dynamicalLaw
lawKind geometricOpticsLimitLaw = limitLaw
lawKind acousticLimitLaw = limitLaw
lawKind standardModelGaugeLaw = symmetryLaw
lawKind anomalyCancellationLaw = constraintLaw
lawKind higgsMechanismLaw = dynamicalLaw
lawKind yukawaFlavourLaw = constitutiveLaw
lawKind ckmPmnsLaw = calibrationLaw
lawKind gaugeRunningLaw = effectiveLaw
lawKind atomicSpectrumLaw = dynamicalLaw
lawKind shellRecurrenceLaw = effectiveLaw
lawKind molecularAssemblyLaw = effectiveLaw
lawKind dimensionalConsistencyLaw = constraintLaw
lawKind metrologyTraceabilityLaw = calibrationLaw
lawKind renormalisationGroupLaw = limitLaw
lawKind discreteContinuumLimitLaw = limitLaw
lawKind quantumClassicalLimitLaw = limitLaw
lawKind kineticFluidLimitLaw = limitLaw
lawKind microscopicThermodynamicLimitLaw = limitLaw

-- Conservative repository-facing status.  This is not a judgement about the
-- established scientific law; it records the current DASHI proof/authority lane.
lawStatus : CanonicalPhysicalLaw → LawClaimStatus
lawStatus causalIntervalLaw = exactStructuralTheorem
lawStatus LorentzInvarianceLaw = exactStructuralTheorem
lawStatus geodesicLaw = conditionalAnalyticBridge
lawStatus newtonMomentumLaw = effectiveModelWithAssumptions
lawStatus eulerLagrangeLaw = exactStructuralTheorem
lawStatus hamiltonEquationLaw = conditionalAnalyticBridge
lawStatus noetherLaw = conditionalAnalyticBridge
lawStatus schrodingerLaw = conditionalAnalyticBridge
lawStatus unitaryEvolutionLaw = conditionalAnalyticBridge
lawStatus bornProbabilityLaw = empiricalCalibrationRequired
lawStatus diracLaw = exactStructuralTheorem
lawStatus microcausalityLaw = externalAuthorityRequired
lawStatus aqftIsotonyLaw = externalAuthorityRequired
lawStatus aqftTimeSliceLaw = externalAuthorityRequired
lawStatus gaugeCovarianceLaw = exactStructuralTheorem
lawStatus gaugeBianchiLaw = exactStructuralTheorem
lawStatus homogeneousMaxwellLaw = conditionalAnalyticBridge
lawStatus inhomogeneousMaxwellLaw = externalAuthorityRequired
lawStatus chargeConservationLaw = externalAuthorityRequired
lawStatus lorentzForceLaw = empiricalCalibrationRequired
lawStatus yangMillsEquationLaw = conditionalAnalyticBridge
lawStatus covariantCurrentLaw = conditionalAnalyticBridge
lawStatus strongInteractionLaw = empiricalCalibrationRequired
lawStatus weakInteractionLaw = empiricalCalibrationRequired
lawStatus einsteinEquationLaw = conditionalAnalyticBridge
lawStatus contractedBianchiLaw = exactStructuralTheorem
lawStatus stressEnergyConservationLaw = conditionalAnalyticBridge
lawStatus newtonianGravityLimitLaw = conditionalAnalyticBridge
lawStatus schwarzschildVacuumLaw = conditionalAnalyticBridge
lawStatus friedmannLaw = effectiveModelWithAssumptions
lawStatus gravitationalWaveLaw = conditionalAnalyticBridge
lawStatus zerothThermodynamicLaw = effectiveModelWithAssumptions
lawStatus firstThermodynamicLaw = effectiveModelWithAssumptions
lawStatus secondThermodynamicLaw = effectiveModelWithAssumptions
lawStatus thirdThermodynamicLaw = effectiveModelWithAssumptions
lawStatus equationOfStateLaw = empiricalCalibrationRequired
lawStatus ensembleLaw = conditionalAnalyticBridge
lawStatus thermodynamicLimitLaw = conditionalAnalyticBridge
lawStatus fluctuationDissipationLaw = effectiveModelWithAssumptions
lawStatus onsagerTransportLaw = effectiveModelWithAssumptions
lawStatus detailedBalanceLaw = effectiveModelWithAssumptions
lawStatus massBalanceLaw = exactStructuralTheorem
lawStatus momentumBalanceLaw = exactStructuralTheorem
lawStatus energyBalanceLaw = exactStructuralTheorem
lawStatus hookeElasticityLaw = empiricalCalibrationRequired
lawStatus fickDiffusionLaw = empiricalCalibrationRequired
lawStatus fourierHeatLaw = empiricalCalibrationRequired
lawStatus navierStokesWeakLaw = concreteFiniteInstance
lawStatus navierStokesRegularityLaw = openMathematicalProblem
lawStatus reactionDiffusionLaw = effectiveModelWithAssumptions
lawStatus magnetohydrodynamicLaw = effectiveModelWithAssumptions
lawStatus waveEquationLaw = conditionalAnalyticBridge
lawStatus geometricOpticsLimitLaw = conditionalAnalyticBridge
lawStatus acousticLimitLaw = conditionalAnalyticBridge
lawStatus standardModelGaugeLaw = notPromoted
lawStatus anomalyCancellationLaw = concreteFiniteInstance
lawStatus higgsMechanismLaw = conditionalAnalyticBridge
lawStatus yukawaFlavourLaw = empiricalCalibrationRequired
lawStatus ckmPmnsLaw = empiricalCalibrationRequired
lawStatus gaugeRunningLaw = conditionalAnalyticBridge
lawStatus atomicSpectrumLaw = conditionalAnalyticBridge
lawStatus shellRecurrenceLaw = conditionalAnalyticBridge
lawStatus molecularAssemblyLaw = conditionalAnalyticBridge
lawStatus dimensionalConsistencyLaw = exactStructuralTheorem
lawStatus metrologyTraceabilityLaw = empiricalCalibrationRequired
lawStatus renormalisationGroupLaw = conditionalAnalyticBridge
lawStatus discreteContinuumLimitLaw = conditionalAnalyticBridge
lawStatus quantumClassicalLimitLaw = conditionalAnalyticBridge
lawStatus kineticFluidLimitLaw = conditionalAnalyticBridge
lawStatus microscopicThermodynamicLimitLaw = conditionalAnalyticBridge

canonicalPhysicalLawAtlas : List CanonicalPhysicalLaw
canonicalPhysicalLawAtlas =
  causalIntervalLaw ∷ LorentzInvarianceLaw ∷ geodesicLaw
  ∷ newtonMomentumLaw ∷ eulerLagrangeLaw ∷ hamiltonEquationLaw ∷ noetherLaw
  ∷ schrodingerLaw ∷ unitaryEvolutionLaw ∷ bornProbabilityLaw ∷ diracLaw
  ∷ microcausalityLaw ∷ aqftIsotonyLaw ∷ aqftTimeSliceLaw
  ∷ gaugeCovarianceLaw ∷ gaugeBianchiLaw
  ∷ homogeneousMaxwellLaw ∷ inhomogeneousMaxwellLaw
  ∷ chargeConservationLaw ∷ lorentzForceLaw
  ∷ yangMillsEquationLaw ∷ covariantCurrentLaw
  ∷ strongInteractionLaw ∷ weakInteractionLaw
  ∷ einsteinEquationLaw ∷ contractedBianchiLaw ∷ stressEnergyConservationLaw
  ∷ newtonianGravityLimitLaw ∷ schwarzschildVacuumLaw ∷ friedmannLaw
  ∷ gravitationalWaveLaw
  ∷ zerothThermodynamicLaw ∷ firstThermodynamicLaw
  ∷ secondThermodynamicLaw ∷ thirdThermodynamicLaw ∷ equationOfStateLaw
  ∷ ensembleLaw ∷ thermodynamicLimitLaw ∷ fluctuationDissipationLaw
  ∷ onsagerTransportLaw ∷ detailedBalanceLaw
  ∷ massBalanceLaw ∷ momentumBalanceLaw ∷ energyBalanceLaw
  ∷ hookeElasticityLaw ∷ fickDiffusionLaw ∷ fourierHeatLaw
  ∷ navierStokesWeakLaw ∷ navierStokesRegularityLaw ∷ reactionDiffusionLaw
  ∷ magnetohydrodynamicLaw ∷ waveEquationLaw ∷ geometricOpticsLimitLaw
  ∷ acousticLimitLaw
  ∷ standardModelGaugeLaw ∷ anomalyCancellationLaw ∷ higgsMechanismLaw
  ∷ yukawaFlavourLaw ∷ ckmPmnsLaw ∷ gaugeRunningLaw
  ∷ atomicSpectrumLaw ∷ shellRecurrenceLaw ∷ molecularAssemblyLaw
  ∷ dimensionalConsistencyLaw ∷ metrologyTraceabilityLaw
  ∷ renormalisationGroupLaw ∷ discreteContinuumLimitLaw
  ∷ quantumClassicalLimitLaw ∷ kineticFluidLimitLaw
  ∷ microscopicThermodynamicLimitLaw ∷ []
