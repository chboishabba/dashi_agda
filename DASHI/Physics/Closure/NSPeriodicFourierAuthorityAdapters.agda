module DASHI.Physics.Closure.NSPeriodicFourierAuthorityAdapters where

open import Agda.Primitive using (Level; lsuc)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicFourierAnalyticAuthorityBoundary as Authority

------------------------------------------------------------------------
-- Selected-state adapters for standard periodic harmonic-analysis theorems.
------------------------------------------------------------------------

record SelectedPeriodicHarmonicAuthority
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index Shell Time State : Set i) : Set (lsuc i) where
  field
    authority :
      Authority.PublishedPeriodicHarmonicAnalysisAuthority
        {ℓProp = i}
        Index Shell Time State (Scalar A) (_≤_ A)

    selectedState : Index → Time → State

    selectedStateAdmissible : ∀ q τ →
      Authority.Admissible authority q τ (selectedState q τ)

open SelectedPeriodicHarmonicAuthority public

selectedShellCurlEstimate :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Shell Time State : Set i} →
  (S : SelectedPeriodicHarmonicAuthority A Index Shell Time State) →
  ∀ shell q τ →
  _≤_ A
    (Authority.shellGradientL2 (authority S) shell (selectedState S q τ))
    (Authority.shellVelocityL2 (authority S) shell (selectedState S q τ))
selectedShellCurlEstimate S shell q τ =
  Authority.shellCurlEstimate (authority S) shell (selectedState S q τ)

selectedShellBernsteinEstimate :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Shell Time State : Set i} →
  (S : SelectedPeriodicHarmonicAuthority A Index Shell Time State) →
  ∀ shell q τ →
  _≤_ A
    (Authority.shellVorticityLInfinity
      (authority S) shell (selectedState S q τ))
    (Authority.shellGradientL2
      (authority S) shell (selectedState S q τ))
selectedShellBernsteinEstimate S shell q τ =
  Authority.shellBernsteinEstimate (authority S) shell (selectedState S q τ)

selectedBonyLowHighEstimate :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Shell Time State : Set i} →
  (S : SelectedPeriodicHarmonicAuthority A Index Shell Time State) →
  ∀ q τ →
  _≤_ A
    (Authority.nearLowHigh (authority S) q τ (selectedState S q τ))
    (Authority.nearLowHighProduct
      (authority S) q τ (selectedState S q τ))
selectedBonyLowHighEstimate S q τ =
  Authority.bonyLowHighEstimate (authority S) q τ (selectedState S q τ)
    (selectedStateAdmissible S q τ)

selectedBonyHighLowEstimate :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Shell Time State : Set i} →
  (S : SelectedPeriodicHarmonicAuthority A Index Shell Time State) →
  ∀ q τ →
  _≤_ A
    (Authority.nearHighLow (authority S) q τ (selectedState S q τ))
    (Authority.nearHighLowProduct
      (authority S) q τ (selectedState S q τ))
selectedBonyHighLowEstimate S q τ =
  Authority.bonyHighLowEstimate (authority S) q τ (selectedState S q τ)
    (selectedStateAdmissible S q τ)

selectedBonyHighHighEstimate :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Shell Time State : Set i} →
  (S : SelectedPeriodicHarmonicAuthority A Index Shell Time State) →
  ∀ q τ →
  _≤_ A
    (Authority.nearHighHigh (authority S) q τ (selectedState S q τ))
    (Authority.nearHighHighProduct
      (authority S) q τ (selectedState S q τ))
selectedBonyHighHighEstimate S q τ =
  Authority.bonyHighHighEstimate (authority S) q τ (selectedState S q τ)
    (selectedStateAdmissible S q τ)

selectedFarLowCommutatorEstimate :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Shell Time State : Set i} →
  (S : SelectedPeriodicHarmonicAuthority A Index Shell Time State) →
  ∀ q τ →
  _≤_ A
    (Authority.farLowCommutator
      (authority S) q τ (selectedState S q τ))
    (Authority.multiplierDifference
      (authority S) q τ (selectedState S q τ))
selectedFarLowCommutatorEstimate S q τ =
  Authority.farLowCommutatorEstimate
    (authority S) q τ (selectedState S q τ)
    (selectedStateAdmissible S q τ)

selectedMultiplierMeanValueEstimate :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Shell Time State : Set i} →
  (S : SelectedPeriodicHarmonicAuthority A Index Shell Time State) →
  ∀ q τ →
  _≤_ A
    (Authority.multiplierDifference
      (authority S) q τ (selectedState S q τ))
    (Authority.meanValueMajorant
      (authority S) q τ (selectedState S q τ))
selectedMultiplierMeanValueEstimate S q τ =
  Authority.multiplierMeanValueEstimate
    (authority S) q τ (selectedState S q τ)
    (selectedStateAdmissible S q τ)

selectedHighSobolevTailEstimate :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Shell Time State : Set i} →
  (S : SelectedPeriodicHarmonicAuthority A Index Shell Time State) →
  ∀ q τ →
  _≤_ A
    (Authority.highFiveHalvesTail
      (authority S) q τ (selectedState S q τ))
    (Authority.hSobolevNorm
      (authority S) q τ (selectedState S q τ))
selectedHighSobolevTailEstimate S q τ =
  Authority.highSobolevTailEstimate
    (authority S) q τ (selectedState S q τ)
    (selectedStateAdmissible S q τ)

selectedFarHighLeftEstimate :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Shell Time State : Set i} →
  (S : SelectedPeriodicHarmonicAuthority A Index Shell Time State) →
  ∀ q τ →
  _≤_ A
    (Authority.farHighLeft
      (authority S) q τ (selectedState S q τ))
    (Authority.farHighSobolevMajorant
      (authority S) q τ (selectedState S q τ))
selectedFarHighLeftEstimate S q τ =
  Authority.farHighLeftEstimate
    (authority S) q τ (selectedState S q τ)
    (selectedStateAdmissible S q τ)

selectedFarHighRightEstimate :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Shell Time State : Set i} →
  (S : SelectedPeriodicHarmonicAuthority A Index Shell Time State) →
  ∀ q τ →
  _≤_ A
    (Authority.farHighRight
      (authority S) q τ (selectedState S q τ))
    (Authority.farHighSobolevMajorant
      (authority S) q τ (selectedState S q τ))
selectedFarHighRightEstimate S q τ =
  Authority.farHighRightEstimate
    (authority S) q τ (selectedState S q τ)
    (selectedStateAdmissible S q τ)
