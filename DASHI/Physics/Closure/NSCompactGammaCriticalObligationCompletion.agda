module DASHI.Physics.Closure.NSCompactGammaCriticalObligationCompletion where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaFourCriticalObligations
open import DASHI.Physics.Closure.NSCompactGammaFrontierAttackLemmas

------------------------------------------------------------------------
-- 1. Iterated two-sided shell decay from adjacent Fourier-triad transport.
--
-- The analytic input is now only the one-shell Fourier-triad estimate in each
-- direction.  The arbitrary shell-distance theorem is derived by induction;
-- it is no longer an independent field that can disagree with the dynamics.
------------------------------------------------------------------------

record FourierTriadAdjacentDecay
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i) : Set (lsuc i) where
  field
    Time State : Set i
    selectedState : Index → Time → State

    ShellAtOffset : Index → Nat → Nat → Set i
    centreShell : Index → Set i

    WeightedShell : Set i → State → Scalar A
    Envelope : Index → Time → Scalar A
    StepCoefficient : Scalar A
    ScaleCoefficient : Nat → Scalar A

    scaleZero : ScaleCoefficient zero ≡ StepCoefficient
    scaleStep : ∀ n →
      ScaleCoefficient (suc n) ≡
      _+_ A StepCoefficient (ScaleCoefficient n)

    centreBound : ∀ q τ shell →
      centreShell q →
      _≤_ A (WeightedShell shell (selectedState q τ)) (Envelope q τ)

    adjacentLeft : ∀ q τ left right n m →
      ShellAtOffset q n m right →
      ShellAtOffset q (suc n) m left →
      _≤_ A
        (WeightedShell left (selectedState q τ))
        (_+_ A StepCoefficient
          (WeightedShell right (selectedState q τ)))

    adjacentRight : ∀ q τ left right n m →
      ShellAtOffset q n m left →
      ShellAtOffset q n (suc m) right →
      _≤_ A
        (WeightedShell right (selectedState q τ))
        (_+_ A StepCoefficient
          (WeightedShell left (selectedState q τ)))

    leftComposition : ∀ q τ shell inner n m →
      ShellAtOffset q (suc n) m shell →
      ShellAtOffset q n m inner →
      _≤_ A
        (WeightedShell inner (selectedState q τ))
        (_+_ A (ScaleCoefficient n) (Envelope q τ)) →
      _≤_ A
        (WeightedShell shell (selectedState q τ))
        (_+_ A (ScaleCoefficient (suc n)) (Envelope q τ))

    rightComposition : ∀ q τ shell inner n m →
      ShellAtOffset q n (suc m) shell →
      ShellAtOffset q n m inner →
      _≤_ A
        (WeightedShell inner (selectedState q τ))
        (_+_ A (ScaleCoefficient m) (Envelope q τ)) →
      _≤_ A
        (WeightedShell shell (selectedState q τ))
        (_+_ A (ScaleCoefficient (suc m)) (Envelope q τ))

    centreAsOffset : ∀ q → centreShell q → ShellAtOffset q zero zero (centreShell q)

open FourierTriadAdjacentDecay public

-- A path witness keeps the shell reached after each left/right triad step tied
-- to the same target packet and the same trajectory.
record LeftTriadPath
    {i : Level}
    {A : AbsorptionArithmetic}
    {Index : Set i}
    (D : FourierTriadAdjacentDecay A Index)
    (q : Index) (distance : Nat) : Set (lsuc i) where
  field
    shell : Nat → Set i
    atCentre : centreShell D q
    offset : ∀ n → ShellAtOffset D q n zero (shell n)

open LeftTriadPath public

record RightTriadPath
    {i : Level}
    {A : AbsorptionArithmetic}
    {Index : Set i}
    (D : FourierTriadAdjacentDecay A Index)
    (q : Index) (distance : Nat) : Set (lsuc i) where
  field
    shell : Nat → Set i
    atCentre : centreShell D q
    offset : ∀ n → ShellAtOffset D q zero n (shell n)

open RightTriadPath public

iterated-left-triad-decay :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    (D : FourierTriadAdjacentDecay A Index)
    (q : Index) (τ : Time D) (distance : Nat)
    (P : LeftTriadPath D q distance) →
  _≤_ A
    (WeightedShell D (LeftTriadPath.shell P distance)
      (selectedState D q τ))
    (_+_ A (ScaleCoefficient D distance) (Envelope D q τ))
iterated-left-triad-decay D q τ zero P
  rewrite scaleZero D =
  centreBound D q τ (LeftTriadPath.shell P zero) (LeftTriadPath.atCentre P)
iterated-left-triad-decay D q τ (suc n) P =
  leftComposition D q τ
    (LeftTriadPath.shell P (suc n))
    (LeftTriadPath.shell P n)
    n zero
    (LeftTriadPath.offset P (suc n))
    (LeftTriadPath.offset P n)
    (iterated-left-triad-decay D q τ n P)

iterated-right-triad-decay :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    (D : FourierTriadAdjacentDecay A Index)
    (q : Index) (τ : Time D) (distance : Nat)
    (P : RightTriadPath D q distance) →
  _≤_ A
    (WeightedShell D (RightTriadPath.shell P distance)
      (selectedState D q τ))
    (_+_ A (ScaleCoefficient D distance) (Envelope D q τ))
iterated-right-triad-decay D q τ zero P
  rewrite scaleZero D =
  centreBound D q τ (RightTriadPath.shell P zero) (RightTriadPath.atCentre P)
iterated-right-triad-decay D q τ (suc n) P =
  rightComposition D q τ
    (RightTriadPath.shell P (suc n))
    (RightTriadPath.shell P n)
    zero n
    (RightTriadPath.offset P (suc n))
    (RightTriadPath.offset P n)
    (iterated-right-triad-decay D q τ n P)

------------------------------------------------------------------------
-- 2. Raw near/tail inequality with a strictly positive surviving margin.
--
-- This packages the exact sign requirement: near gain is split into the tail
-- payment plus a named positive remainder.  The already-checked ordered
-- cancellation theorem then yields the Route-B inequality.
------------------------------------------------------------------------

record PositiveSurvivingMargin
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i)
    (G : RawGammaNearTailInequality A Index) : Set (lsuc i) where
  field
    Positive : Scalar A → Set i
    marginPositive : ∀ q τ → Positive (survivingMargin G q τ)
    tailPaidInsideNearGain : ∀ q τ → Set i

open PositiveSurvivingMargin public

raw-near-tail-with-positive-surviving-margin :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    (G : RawGammaNearTailInequality A Index)
    (P : PositiveSurvivingMargin A Index G) →
  Σ (∀ q τ →
      _≤_ A
        (_+_ A (gammaPotentialDerivative G q τ)
          (survivingMargin G q τ))
        (_+_ A (gammaDissipation G q τ) (gammaForcing G q τ)))
    (λ _ → ∀ q τ → Positive P (survivingMargin G q τ))
raw-near-tail-with-positive-surviving-margin G P =
  gamma-near-tail-cancellation G , marginPositive P

------------------------------------------------------------------------
-- 3. One official seven-parameter tuple.
--
-- The numbers are intentionally fixed in one place.  Feasibility still means
-- the actual five analytic conditions hold for this tuple; unlike the previous
-- interface, downstream code cannot choose a different tuple for each lemma.
------------------------------------------------------------------------

record OfficialSevenParameterNumerals
    {i : Level}
    (A : AbsorptionArithmetic) : Set (lsuc i) where
  field
    eight one two : Scalar A

open OfficialSevenParameterNumerals public

canonicalSevenParameterTuple :
  ∀ {i} {A : AbsorptionArithmetic} →
  OfficialSevenParameterNumerals {i} A →
  CompactGammaParameterTuple {i} A
canonicalSevenParameterTuple N = record
  { radius = eight N
  ; gammaFloor = one N
  ; energyFloor = one N
  ; offPacketCeiling = one N
  ; alphaEnergy = two N
  ; alphaGamma = two N
  ; alphaOffPacket = one N
  }

record CanonicalTupleFeasibility
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i)
    (N : OfficialSevenParameterNumerals {i} A) : Set (lsuc i) where
  field
    feasibility : SharedParameterFeasibility A Index (canonicalSevenParameterTuple N)

open CanonicalTupleFeasibility public

canonical-seven-parameter-tuple-closes-all-local-conditions :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    (N : OfficialSevenParameterNumerals {i} A)
    (F : CanonicalTupleFeasibility A Index N) →
  SimultaneousLocalClosure A Index
    (feasibleTuple-to-sharedParameters
      (canonicalSevenParameterTuple N) (feasibility F))
canonical-seven-parameter-tuple-closes-all-local-conditions N F =
  feasibleTuple-to-simultaneousClosure
    (canonicalSevenParameterTuple N) (feasibility F)

------------------------------------------------------------------------
-- 4. Rigorous obstruction to the "all official data initially admissible"
-- route.
--
-- The zero solution is smooth, divergence-free and finite-energy.  Whenever
-- compact-Gamma admissibility requires strictly positive packet energy, the
-- zero solution cannot be initially admissible.  Hence Route 1 cannot cover the
-- official class.  This does not obstruct a later-entry theorem or a genuinely
-- universal replacement mechanism.
------------------------------------------------------------------------

record ZeroDatumPacketFloorObstruction
    {i : Level}
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    initialTime : Time S
    zeroDatum : InitialDatum S
    zeroSolution : Solution S

    zeroIsOfficial : SmoothDivergenceFreeFiniteEnergy S zeroDatum
    zeroSolves : SolvesFrom S zeroDatum zeroSolution

    PacketEnergyPositive : Solution S → Time S → Set i
    admissibleImpliesPositivePacketEnergy :
      CompactGammaAdmissible S zeroSolution initialTime →
      PacketEnergyPositive zeroSolution initialTime

    zeroPacketEnergyNotPositive :
      PacketEnergyPositive zeroSolution initialTime → ⊥

open ZeroDatumPacketFloorObstruction public

zero-datum-refutes-all-data-initial-admissibility :
  ∀ {i} {S : OfficialInitialDataSetting i} →
  ZeroDatumPacketFloorObstruction S →
  AllDataInitiallyAdmissible S → ⊥
zero-datum-refutes-all-data-initial-admissibility O A₀ =
  zeroPacketEnergyNotPositive O
    (admissibleImpliesPositivePacketEnergy O
      (everyOfficialDatumStartsAdmissible A₀
        (zeroDatum O)
        (zeroSolution O)
        (zeroIsOfficial O)
        (zeroSolves O)))

record OfficialCoverageAfterInitialObstruction
    {i : Level}
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    zeroObstruction : ZeroDatumPacketFloorObstruction S
    coverage : OfficialDataCoverage S

open OfficialCoverageAfterInitialObstruction public

-- Once the zero-data obstruction is present, any surviving official-data route
-- must be either entry before singularity or a universal replacement mechanism.
official-coverage-must-use-entry-or-replacement :
  ∀ {i} {S : OfficialInitialDataSetting i} →
  OfficialCoverageAfterInitialObstruction S →
  EverySolutionEntersBeforeSingularity S
  ⊎ UniversalReplacementMechanism S
official-coverage-must-use-entry-or-replacement C with coverage C
... | inj₁ starts =
  ⊥-elim (zero-datum-refutes-all-data-initial-admissibility
    (zeroObstruction C) starts)
  where
  ⊥-elim : ⊥ →
    EverySolutionEntersBeforeSingularity _ ⊎ UniversalReplacementMechanism _
  ⊥-elim ()
... | inj₂ surviving = surviving
