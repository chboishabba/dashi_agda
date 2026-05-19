module DASHI.Analysis.GoldbachFormalObjects where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import DASHI.Arithmetic.WeightedValuationEnergy as WVE using
  ( WeightedValuationEnergySurface
  ; weightedValuationEnergySurface
  )

------------------------------------------------------------------------
-- Goldbach/Δ formal objects.
--
-- This module is intentionally theorem-thin. It packages the programmatic
-- surfaces discussed in the refreshed Dashi thread without claiming a proof
-- of strong Goldbach, RH, or a completed major/minor arc analysis.

record EnergyΔ
  {ℓΔ ℓC ℓW : Level}
  (DeltaState : Set ℓΔ)
  (Carrier : Set ℓC)
  (Weight : Set ℓW) :
  Set (lsuc (ℓΔ ⊔ ℓC ⊔ ℓW)) where
  field
    TΔ : DeltaState → Carrier
    Q̂core : Carrier → Weight

  energy : DeltaState → Weight
  energy δ = Q̂core (TΔ δ)

weightedValuationEnergyΔ :
  (surface : WeightedValuationEnergySurface) →
  EnergyΔ
    (WeightedValuationEnergySurface.Carrier surface)
    (WeightedValuationEnergySurface.Carrier surface)
    Nat
weightedValuationEnergyΔ surface = record
  { TΔ = λ x → x
  ; Q̂core = WeightedValuationEnergySurface.weightedLinearEnergy surface
  }

goldbachWeightedValuationEnergyΔ :
  EnergyΔ
    (WeightedValuationEnergySurface.Carrier weightedValuationEnergySurface)
    (WeightedValuationEnergySurface.Carrier weightedValuationEnergySurface)
    Nat
goldbachWeightedValuationEnergyΔ =
  weightedValuationEnergyΔ weightedValuationEnergySurface

goldbachWeightedValuationEnergyΔMatchesSurface :
  ∀ x →
  EnergyΔ.energy goldbachWeightedValuationEnergyΔ x
  ≡
  WeightedValuationEnergySurface.weightedLinearEnergy
    weightedValuationEnergySurface
    x
goldbachWeightedValuationEnergyΔMatchesSurface x = refl

record GoldbachCone
  {ℓP ℓΔ ℓC ℓW ℓB : Level}
  (Prime : Set ℓP)
  (DeltaState : Set ℓΔ)
  (Carrier : Set ℓC)
  (Weight : Set ℓW)
  (BoundWitness : Weight → Set ℓB)
  (N : Nat)
  (energySurface : EnergyΔ DeltaState Carrier Weight) :
  Set (lsuc (ℓP ⊔ ℓΔ ⊔ ℓC ⊔ ℓW ⊔ ℓB)) where
  open EnergyΔ energySurface public

  field
    primeValue : Prime → Nat
    admissible : Prime → Prime → Set ℓB
    deltaState : ∀ {p q} → admissible p q → DeltaState
    inInterior : ∀ {p q} → admissible p q → Carrier
    sum-law :
      ∀ {p q} →
      (h : admissible p q) →
      primeValue p + primeValue q ≡ N
    energyBound : Weight
    bounded :
      ∀ {p q} →
      (h : admissible p q) →
      BoundWitness (EnergyΔ.energy energySurface (deltaState h))
    symmetric :
      ∀ {p q} →
      admissible p q →
      admissible q p

record GoldbachAmplitude
  {ℓP ℓΔ ℓC ℓW ℓB ℓA : Level}
  (Prime : Set ℓP)
  (DeltaState : Set ℓΔ)
  (Carrier : Set ℓC)
  (Weight : Set ℓW)
  (BoundWitness : Weight → Set ℓB)
  (AmplitudeWeight : Set ℓA)
  (N : Nat)
  (energySurface : EnergyΔ DeltaState Carrier Weight)
  (cone : GoldbachCone Prime DeltaState Carrier Weight BoundWitness N energySurface) :
  Set (lsuc (ℓP ⊔ ℓΔ ⊔ ℓC ⊔ ℓW ⊔ ℓB ⊔ ℓA)) where
  open GoldbachCone cone public

  field
    dampingWeight : Weight
    weightedContribution :
      ∀ {p q} →
      admissible p q →
      AmplitudeWeight
    amplitude : AmplitudeWeight
    nonnegativeWeight : ⊤
    positivityImpliesAdmissiblePair : Set ℓB
    finiteWeightedSupport : ⊤

record GoldbachExistenceWitness
  {ℓP ℓΔ ℓC ℓW ℓB : Level}
  (Prime : Set ℓP)
  (DeltaState : Set ℓΔ)
  (Carrier : Set ℓC)
  (Weight : Set ℓW)
  (BoundWitness : Weight → Set ℓB)
  (N : Nat)
  (energySurface : EnergyΔ DeltaState Carrier Weight)
  (cone : GoldbachCone Prime DeltaState Carrier Weight BoundWitness N energySurface) :
  Set (lsuc (ℓP ⊔ ℓΔ ⊔ ℓC ⊔ ℓW ⊔ ℓB)) where
  open GoldbachCone cone public

  field
    leftPrime : Prime
    rightPrime : Prime
    admissibleWitness : admissible leftPrime rightPrime

  sumWitness : primeValue leftPrime + primeValue rightPrime ≡ N
  sumWitness = sum-law admissibleWitness

  boundedEnergyWitness :
    BoundWitness
      (EnergyΔ.energy energySurface (deltaState admissibleWitness))
  boundedEnergyWitness = bounded admissibleWitness

record BoundedGoldbachExistence
  {ℓP ℓΔ ℓC ℓW ℓB : Level}
  (Prime : Set ℓP)
  (DeltaState : Set ℓΔ)
  (Carrier : Set ℓC)
  (Weight : Set ℓW)
  (BoundWitness : Weight → Set ℓB)
  (N : Nat)
  (energySurface : EnergyΔ DeltaState Carrier Weight)
  (cone : GoldbachCone Prime DeltaState Carrier Weight BoundWitness N energySurface) :
  Set (lsuc (ℓP ⊔ ℓΔ ⊔ ℓC ⊔ ℓW ⊔ ℓB)) where
  field
    searchBound : Nat
    witness :
      GoldbachExistenceWitness
        Prime DeltaState Carrier Weight BoundWitness N energySurface cone

sampleExistenceFromConeWitness :
  ∀
    {ℓP ℓΔ ℓC ℓW ℓB}
    {Prime : Set ℓP}
    {DeltaState : Set ℓΔ}
    {Carrier : Set ℓC}
    {Weight : Set ℓW}
    {BoundWitness : Weight → Set ℓB}
    {N : Nat}
    {energySurface : EnergyΔ DeltaState Carrier Weight}
    {cone : GoldbachCone Prime DeltaState Carrier Weight BoundWitness N energySurface} →
  (leftPrime : Prime) →
  (rightPrime : Prime) →
  GoldbachCone.admissible cone leftPrime rightPrime →
  GoldbachExistenceWitness
    Prime DeltaState Carrier Weight BoundWitness N energySurface cone
sampleExistenceFromConeWitness leftPrime rightPrime admissibleWitness =
  record
    { leftPrime = leftPrime
    ; rightPrime = rightPrime
    ; admissibleWitness = admissibleWitness
    }

record GoldbachTheoremLadder
  {ℓP ℓΔ ℓC ℓW ℓB ℓA : Level}
  (Prime : Set ℓP)
  (DeltaState : Set ℓΔ)
  (Carrier : Set ℓC)
  (Weight : Set ℓW)
  (BoundWitness : Weight → Set ℓB)
  (AmplitudeWeight : Set ℓA)
  (N : Nat)
  (energySurface : EnergyΔ DeltaState Carrier Weight)
  (cone : GoldbachCone Prime DeltaState Carrier Weight BoundWitness N energySurface)
  (amplitude : GoldbachAmplitude Prime DeltaState Carrier Weight BoundWitness AmplitudeWeight N energySurface cone) :
  Set (lsuc (ℓP ⊔ ℓΔ ⊔ ℓC ⊔ ℓW ⊔ ℓB ⊔ ℓA)) where
  field
    existenceSurface :
      BoundedGoldbachExistence
        Prime DeltaState Carrier Weight BoundWitness N energySurface cone
    positivitySurface : Set ℓB
    strongerPositivitySurface : Set ℓB
    positivityImpliesConeGoldbach : Set ℓB
    coneExhaustionImpliesOrdinaryGoldbach : Set ℓB
    majorMinorArcCriterionSurface : Set ℓB
    weightedPrimeWaveSurface : Set ℓB
    multiplicativeZetaShadowSurface : Set ℓB
    unresolvedAnalyticGap : Set ℓB
    noStrongGoldbachProofClaim : ⊤
    noRiemannHypothesisClaim : ⊤

record GoldbachProgramPack
  {ℓP ℓΔ ℓC ℓW ℓB ℓA : Level}
  (Prime : Set ℓP)
  (DeltaState : Set ℓΔ)
  (Carrier : Set ℓC)
  (Weight : Set ℓW)
  (BoundWitness : Weight → Set ℓB)
  (AmplitudeWeight : Set ℓA)
  (N : Nat) :
  Set (lsuc (ℓP ⊔ ℓΔ ⊔ ℓC ⊔ ℓW ⊔ ℓB ⊔ ℓA)) where
  field
    energySurface :
      EnergyΔ DeltaState Carrier Weight
    cone :
      GoldbachCone Prime DeltaState Carrier Weight BoundWitness N energySurface
    amplitude :
      GoldbachAmplitude
        Prime DeltaState Carrier Weight BoundWitness AmplitudeWeight
        N energySurface cone
    theoremLadder :
      GoldbachTheoremLadder
        Prime DeltaState Carrier Weight BoundWitness AmplitudeWeight
        N energySurface cone amplitude
    analysisOnly : ⊤
    noSolvedGoldbachClaim : ⊤
    noSolvedRHClaim : ⊤

goldbachProgramIsAnalysisOnly :
  ∀
    {ℓP ℓΔ ℓC ℓW ℓB ℓA}
    {Prime : Set ℓP}
    {DeltaState : Set ℓΔ}
    {Carrier : Set ℓC}
    {Weight : Set ℓW}
    {BoundWitness : Weight → Set ℓB}
    {AmplitudeWeight : Set ℓA}
    {N : Nat} →
  GoldbachProgramPack Prime DeltaState Carrier Weight BoundWitness AmplitudeWeight N →
  ⊤
goldbachProgramIsAnalysisOnly pack =
  GoldbachProgramPack.analysisOnly pack

------------------------------------------------------------------------
-- Small sample-side witness lane
------------------------------------------------------------------------

data SamplePrime : Set where
  p₂ : SamplePrime
  p₃ : SamplePrime
  p₅ : SamplePrime

data SampleGoldbachAdmissible : SamplePrime → SamplePrime → Set where
  witness₂₂ : SampleGoldbachAdmissible p₂ p₂

data SampleGoldbachAdmissible8 : SamplePrime → SamplePrime → Set where
  witness₃₅ : SampleGoldbachAdmissible8 p₃ p₅
  witness₅₃ : SampleGoldbachAdmissible8 p₅ p₃

sampleGoldbachCone :
  GoldbachCone
    SamplePrime
    (WeightedValuationEnergySurface.Carrier weightedValuationEnergySurface)
    (WeightedValuationEnergySurface.Carrier weightedValuationEnergySurface)
    Nat
    (λ _ → ⊤)
    4
    goldbachWeightedValuationEnergyΔ
sampleGoldbachCone = record
  { primeValue = λ { p₂ → 2 ; p₃ → 3 ; p₅ → 5 }
  ; admissible = SampleGoldbachAdmissible
  ; deltaState = λ { witness₂₂ → 2 }
  ; inInterior = λ { witness₂₂ → 2 }
  ; sum-law = λ { witness₂₂ → refl }
  ; energyBound =
      EnergyΔ.energy goldbachWeightedValuationEnergyΔ 2
  ; bounded = λ { witness₂₂ → tt }
  ; symmetric = λ { witness₂₂ → witness₂₂ }
  }

sampleGoldbachExistenceWitness :
  GoldbachExistenceWitness
    SamplePrime
    (WeightedValuationEnergySurface.Carrier weightedValuationEnergySurface)
    (WeightedValuationEnergySurface.Carrier weightedValuationEnergySurface)
    Nat
    (λ _ → ⊤)
    4
    goldbachWeightedValuationEnergyΔ
    sampleGoldbachCone
sampleGoldbachExistenceWitness =
  sampleExistenceFromConeWitness p₂ p₂ witness₂₂

sampleGoldbachBoundedExistence :
  BoundedGoldbachExistence
    SamplePrime
    (WeightedValuationEnergySurface.Carrier weightedValuationEnergySurface)
    (WeightedValuationEnergySurface.Carrier weightedValuationEnergySurface)
    Nat
    (λ _ → ⊤)
    4
    goldbachWeightedValuationEnergyΔ
    sampleGoldbachCone
sampleGoldbachBoundedExistence = record
  { searchBound = 4
  ; witness = sampleGoldbachExistenceWitness
  }

sampleGoldbachCone8 :
  GoldbachCone
    SamplePrime
    (WeightedValuationEnergySurface.Carrier weightedValuationEnergySurface)
    (WeightedValuationEnergySurface.Carrier weightedValuationEnergySurface)
    Nat
    (λ _ → ⊤)
    8
    goldbachWeightedValuationEnergyΔ
sampleGoldbachCone8 = record
  { primeValue = λ { p₂ → 2 ; p₃ → 3 ; p₅ → 5 }
  ; admissible = SampleGoldbachAdmissible8
  ; deltaState = λ { witness₃₅ → 3 ; witness₅₃ → 5 }
  ; inInterior = λ { witness₃₅ → 3 ; witness₅₃ → 5 }
  ; sum-law = λ { witness₃₅ → refl ; witness₅₃ → refl }
  ; energyBound =
      EnergyΔ.energy goldbachWeightedValuationEnergyΔ 5
  ; bounded = λ { witness₃₅ → tt ; witness₅₃ → tt }
  ; symmetric = λ { witness₃₅ → witness₅₃ ; witness₅₃ → witness₃₅ }
  }

sampleGoldbachExistenceWitness8 :
  GoldbachExistenceWitness
    SamplePrime
    (WeightedValuationEnergySurface.Carrier weightedValuationEnergySurface)
    (WeightedValuationEnergySurface.Carrier weightedValuationEnergySurface)
    Nat
    (λ _ → ⊤)
    8
    goldbachWeightedValuationEnergyΔ
    sampleGoldbachCone8
sampleGoldbachExistenceWitness8 =
  sampleExistenceFromConeWitness p₃ p₅ witness₃₅

sampleGoldbachBoundedExistence8 :
  BoundedGoldbachExistence
    SamplePrime
    (WeightedValuationEnergySurface.Carrier weightedValuationEnergySurface)
    (WeightedValuationEnergySurface.Carrier weightedValuationEnergySurface)
    Nat
    (λ _ → ⊤)
    8
    goldbachWeightedValuationEnergyΔ
    sampleGoldbachCone8
sampleGoldbachBoundedExistence8 = record
  { searchBound = 8
  ; witness = sampleGoldbachExistenceWitness8
  }
