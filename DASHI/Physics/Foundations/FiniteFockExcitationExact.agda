module DASHI.Physics.Foundations.FiniteFockExcitationExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Finite bosonic and fermionic Fock truncations.

data BosonOccupation : Set where
  zeroBosons : BosonOccupation
  oneBoson : BosonOccupation
  twoBosons : BosonOccupation

data FermionOccupation : Set where
  zeroFermions : FermionOccupation
  oneFermion : FermionOccupation

data CreationResult (A : Set) : Set where
  creationSucceeded : A → CreationResult A
  creationBlocked : CreationResult A

createBoson : BosonOccupation → CreationResult BosonOccupation
createBoson zeroBosons = creationSucceeded oneBoson
createBoson oneBoson = creationSucceeded twoBosons
createBoson twoBosons = creationBlocked

annihilateBoson : BosonOccupation → CreationResult BosonOccupation
annihilateBoson zeroBosons = creationBlocked
annihilateBoson oneBoson = creationSucceeded zeroBosons
annihilateBoson twoBosons = creationSucceeded oneBoson

createFermion : FermionOccupation → CreationResult FermionOccupation
createFermion zeroFermions = creationSucceeded oneFermion
createFermion oneFermion = creationBlocked

annihilateFermion : FermionOccupation → CreationResult FermionOccupation
annihilateFermion zeroFermions = creationBlocked
annihilateFermion oneFermion = creationSucceeded zeroFermions

fermionCreationIsNilpotentAtOneMode :
  createFermion oneFermion ≡ creationBlocked
fermionCreationIsNilpotentAtOneMode = refl

bosonAndFermionOccupancyRulesDiffer :
  createBoson oneBoson ≡ creationSucceeded twoBosons
  ×
  createFermion oneFermion ≡ creationBlocked
bosonAndFermionOccupancyRulesDiffer = refl , refl

------------------------------------------------------------------------
-- Finite relativistic-dispersion witness.  The Pythagorean triple gives an
-- exact mass-shell relation E^2 = p^2 + m^2 without claiming a continuum
-- representation of the Poincare group.

record DispersionDatum : Set where
  constructor dispersionDatum
  field
    energy : Nat
    momentumMagnitude : Nat
    mass : Nat

open DispersionDatum public

onMassShell : DispersionDatum → Set
onMassShell datum =
  energy datum * energy datum
  ≡
  momentumMagnitude datum * momentumMagnitude datum
  +
  mass datum * mass datum

canonicalMassShellDatum : DispersionDatum
canonicalMassShellDatum = dispersionDatum 5 3 4

canonicalMassShellRelation : onMassShell canonicalMassShellDatum
canonicalMassShellRelation = refl

------------------------------------------------------------------------
-- Stable excitation requires a spectral separation and a decay-channel
-- condition.  Persistence by itself is not enough.

data SpectralIsolation : Set where
  embeddedInContinuum : SpectralIsolation
  isolatedMassShell : SpectralIsolation

data DecayChannelStatus : Set where
  openDecayChannel : DecayChannelStatus
  noKinematicallyOpenDecayChannel : DecayChannelStatus

data ExcitationStatus : Set where
  transientPattern : ExcitationStatus
  metastableExcitation : ExcitationStatus
  stableParticleCandidate : ExcitationStatus

classifyExcitation :
  SpectralIsolation → DecayChannelStatus → ExcitationStatus
classifyExcitation embeddedInContinuum openDecayChannel = transientPattern
classifyExcitation embeddedInContinuum noKinematicallyOpenDecayChannel =
  metastableExcitation
classifyExcitation isolatedMassShell openDecayChannel = metastableExcitation
classifyExcitation isolatedMassShell noKinematicallyOpenDecayChannel =
  stableParticleCandidate

isolatedClosedExcitationIsStableCandidate :
  classifyExcitation
    isolatedMassShell
    noKinematicallyOpenDecayChannel
  ≡
  stableParticleCandidate
isolatedClosedExcitationIsStableCandidate = refl

persistentButEmbeddedPatternIsNotStableParticle :
  classifyExcitation embeddedInContinuum noKinematicallyOpenDecayChannel
  ≡
  metastableExcitation
persistentButEmbeddedPatternIsNotStableParticle = refl

------------------------------------------------------------------------
-- Finite two-point spectral data.  An isolated nonzero weight at one mass label
-- is a discrete pole analogue; it does not supply analytic continuation or a
-- continuum correlation-function theorem.

data MassLabel : Set where
  massZero : MassLabel
  massOne : MassLabel
  massTwo : MassLabel

spectralWeight : MassLabel → Nat
spectralWeight massZero = 0
spectralWeight massOne = 5
spectralWeight massTwo = 0

isolatedMassOneWeightIsFive : spectralWeight massOne ≡ 5
isolatedMassOneWeightIsFive = refl

neighbouringSpectralWeightsVanish :
  spectralWeight massZero ≡ 0
  ×
  spectralWeight massTwo ≡ 0
neighbouringSpectralWeightsVanish = refl , refl

record FiniteFockExcitationBoundary : Set where
  constructor finiteFockExcitationBoundary
  field
    oneParticleWavefunctionIsAlreadyFockSpace : Bool
    oneParticleWavefunctionIsAlreadyFockSpaceIsFalse :
      oneParticleWavefunctionIsAlreadyFockSpace ≡ false

    finiteOccupationTableProvesCanonicalCommutationRelations : Bool
    finiteOccupationTableProvesCanonicalCommutationRelationsIsFalse :
      finiteOccupationTableProvesCanonicalCommutationRelations ≡ false

    exactPythagoreanDispersionProvesLorentzCovariance : Bool
    exactPythagoreanDispersionProvesLorentzCovarianceIsFalse :
      exactPythagoreanDispersionProvesLorentzCovariance ≡ false

    persistentPatternAutomaticallyIsParticle : Bool
    persistentPatternAutomaticallyIsParticleIsFalse :
      persistentPatternAutomaticallyIsParticle ≡ false

    finiteSpectralWeightIsAnalyticPoleTheorem : Bool
    finiteSpectralWeightIsAnalyticPoleTheoremIsFalse :
      finiteSpectralWeightIsAnalyticPoleTheorem ≡ false

open FiniteFockExcitationBoundary public

canonicalFiniteFockExcitationBoundary : FiniteFockExcitationBoundary
canonicalFiniteFockExcitationBoundary =
  finiteFockExcitationBoundary false refl false refl false refl false refl false refl
