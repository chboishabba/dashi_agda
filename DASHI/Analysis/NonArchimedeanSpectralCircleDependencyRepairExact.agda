module DASHI.Analysis.NonArchimedeanSpectralCircleDependencyRepairExact where

------------------------------------------------------------------------
-- SOURCE-EXACT DEPENDENCY REPAIR FOR `spectral_circle`
--
-- The source file contains substantial orbit and cyclotomic mathematics, but
-- the final `spectral_circle` theorem does not derive the magnitude formula
-- from those lemmas.  Its actual proof path is:
--
--   spectrum membership
--     -> HasEigenvalue
--     -> `twisted_eigenvalue_magnitude n h ...`
--     -> field of `TwistedBlockHypothesis`.
--
-- Thus we keep two dependency graphs separate:
--   (A) the intended derivation from character/orbit/cyclotomic data;
--   (B) the currently checked Lean proof, which consumes the final magnitude
--       as a hypothesis.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)


data SpectralProducer : Set where
  characterAction : SpectralProducer
  orbitOrder : SpectralProducer
  oddOrbitPartition : SpectralProducer
  cyclotomicOddProduct : SpectralProducer
  orbitWeightMagnitude : SpectralProducer
  concreteDFTMonomialWeld : SpectralProducer
  cyclicMonomialSpectrum : SpectralProducer
  assumedSpatialEigenvalueMagnitude : SpectralProducer
  spatialSpectralCircle : SpectralProducer

intendedProducerPath : List SpectralProducer
intendedProducerPath =
  characterAction ∷
  orbitOrder ∷
  oddOrbitPartition ∷
  cyclotomicOddProduct ∷
  orbitWeightMagnitude ∷
  concreteDFTMonomialWeld ∷
  cyclicMonomialSpectrum ∷
  spatialSpectralCircle ∷
  []

checkedLeanTerminalPath : List SpectralProducer
checkedLeanTerminalPath =
  assumedSpatialEigenvalueMagnitude ∷
  spatialSpectralCircle ∷
  []

record DependencyStatus : Set where
  constructor dependencyStatus
  field
    characterActionTheoremExists : Bool
    orbitOrderTheoremExists : Bool
    cyclotomicProductTheoremExists : Bool
    orbitWeightMathematicsExists : Bool
    concreteDFTInfrastructureExists : Bool
    finalSpatialTheoremConsumesFinalMagnitudeHypothesis : Bool
    finalSpatialTheoremDerivesMagnitudeFromOrbitLemmas : Bool
    intendedDependencyChainClosed : Bool

canonicalDependencyStatus : DependencyStatus
canonicalDependencyStatus =
  dependencyStatus
    true true true true true
    true
    false
    false

record PromotionFirewall : Set where
  constructor promotionFirewall
  field
    presenceOfLemmasInSameFileImpliesDependencyUse : Bool
    conditionalFinalTheoremImpliesIntendedDerivationClosed : Bool
    proofOfHypothesisImpliesProofFromItsAdvertisedMotivation : Bool

canonicalPromotionFirewall : PromotionFirewall
canonicalPromotionFirewall =
  promotionFirewall false false false

finalTheoremDoesNotCloseIntendedPath :
  DependencyStatus.intendedDependencyChainClosed canonicalDependencyStatus
  ≡ false
finalTheoremDoesNotCloseIntendedPath = refl

checkedTerminalUsesAssumption :
  DependencyStatus.finalSpatialTheoremConsumesFinalMagnitudeHypothesis
    canonicalDependencyStatus
  ≡ true
checkedTerminalUsesAssumption = refl
