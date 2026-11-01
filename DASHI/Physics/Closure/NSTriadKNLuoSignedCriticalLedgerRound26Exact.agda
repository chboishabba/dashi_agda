module DASHI.Physics.Closure.NSTriadKNLuoSignedCriticalLedgerRound26Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- The finite critical ledger is signed first.  Positive-part taxation is not
-- inserted into the identity.  Each shell owns HH, LH, HL, CC, Com and the
-- two cutoff-boundary coordinates separately.  Multiplying by an arbitrary
-- critical weight and summing a finite shell list preserves the exact balance.
--
-- The shell-weight algebra also proves the relation
--
--   weight * vorticityEnergy = criticalVelocityWeight * velocityEnergy
--
-- from the two exact meanings
--
--   vorticityEnergy = frequencySquared * velocityEnergy,
--   weight * frequencySquared = criticalVelocityWeight.
--
-- Thus the familiar 2^{-q} 2^{2q} = 2^q calculation is represented without
-- division or an ambiguous zero mode.  The homogeneous route explicitly
-- excludes the zero mode; Galilean restoration remains downstream.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool; true)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

record CriticalWeightMeaning : Set where
  constructor critical-weight-meaning
  field
    shellIndex : Nat
    shellWeight : ℚ
    frequencySquared : ℚ
    velocityEnergy : ℚ
    vorticityEnergy : ℚ
    criticalVelocityWeight : ℚ

    vorticityEnergyMeaning :
      vorticityEnergy ≡ frequencySquared * velocityEnergy

    criticalWeightMeaning :
      shellWeight * frequencySquared ≡ criticalVelocityWeight

open CriticalWeightMeaning public

criticalVelocityVorticityWeightIdentity :
  (W : CriticalWeightMeaning) →
  shellWeight W * vorticityEnergy W
  ≡ criticalVelocityWeight W * velocityEnergy W
criticalVelocityVorticityWeightIdentity W =
  trans
    (cong
      (λ energy → shellWeight W * energy)
      (vorticityEnergyMeaning W))
    (trans
      (solve
        ( shellWeight W
        ∷ frequencySquared W
        ∷ velocityEnergy W
        ∷ []))
      (cong
        (λ coefficient → coefficient * velocityEnergy W)
        (criticalWeightMeaning W)))

record SignedCriticalShellCell : Set where
  constructor signed-critical-shell-cell
  field
    criticalWeight : ℚ
    energyRate : ℚ
    dissipation : ℚ

    HHsource LHsource HLsource CCsource ComSource : ℚ
    lowerBoundarySource upperBoundarySource : ℚ

    signedShellBalance :
      energyRate + dissipation
      ≡
      HHsource + LHsource + HLsource + CCsource + ComSource
      + lowerBoundarySource + upperBoundarySource

open SignedCriticalShellCell public

weightedEnergyRate : SignedCriticalShellCell → ℚ
weightedEnergyRate C = criticalWeight C * energyRate C

weightedDissipation : SignedCriticalShellCell → ℚ
weightedDissipation C = criticalWeight C * dissipation C

weightedHH weightedLH weightedHL weightedCC weightedCom :
  SignedCriticalShellCell → ℚ
weightedHH C = criticalWeight C * HHsource C
weightedLH C = criticalWeight C * LHsource C
weightedHL C = criticalWeight C * HLsource C
weightedCC C = criticalWeight C * CCsource C
weightedCom C = criticalWeight C * ComSource C

weightedLowerBoundary weightedUpperBoundary :
  SignedCriticalShellCell → ℚ
weightedLowerBoundary C = criticalWeight C * lowerBoundarySource C
weightedUpperBoundary C = criticalWeight C * upperBoundarySource C

weightedShellBalance :
  (C : SignedCriticalShellCell) →
  weightedEnergyRate C + weightedDissipation C
  ≡
  weightedHH C + weightedLH C + weightedHL C + weightedCC C
  + weightedCom C + weightedLowerBoundary C + weightedUpperBoundary C
weightedShellBalance C =
  trans
    (solve
      ( criticalWeight C
      ∷ energyRate C
      ∷ dissipation C
      ∷ []))
    (trans
      (cong
        (λ total → criticalWeight C * total)
        (signedShellBalance C))
      (solve
        ( criticalWeight C
        ∷ HHsource C ∷ LHsource C ∷ HLsource C ∷ CCsource C
        ∷ ComSource C ∷ lowerBoundarySource C ∷ upperBoundarySource C
        ∷ [])))

sumWeightedEnergyRate : List SignedCriticalShellCell → ℚ
sumWeightedEnergyRate [] = 0ℚ
sumWeightedEnergyRate (C ∷ rest) =
  weightedEnergyRate C + sumWeightedEnergyRate rest

sumWeightedDissipation : List SignedCriticalShellCell → ℚ
sumWeightedDissipation [] = 0ℚ
sumWeightedDissipation (C ∷ rest) =
  weightedDissipation C + sumWeightedDissipation rest

sumWeightedHH : List SignedCriticalShellCell → ℚ
sumWeightedHH [] = 0ℚ
sumWeightedHH (C ∷ rest) = weightedHH C + sumWeightedHH rest

sumWeightedLH : List SignedCriticalShellCell → ℚ
sumWeightedLH [] = 0ℚ
sumWeightedLH (C ∷ rest) = weightedLH C + sumWeightedLH rest

sumWeightedHL : List SignedCriticalShellCell → ℚ
sumWeightedHL [] = 0ℚ
sumWeightedHL (C ∷ rest) = weightedHL C + sumWeightedHL rest

sumWeightedCC : List SignedCriticalShellCell → ℚ
sumWeightedCC [] = 0ℚ
sumWeightedCC (C ∷ rest) = weightedCC C + sumWeightedCC rest

sumWeightedCom : List SignedCriticalShellCell → ℚ
sumWeightedCom [] = 0ℚ
sumWeightedCom (C ∷ rest) = weightedCom C + sumWeightedCom rest

sumWeightedLowerBoundary : List SignedCriticalShellCell → ℚ
sumWeightedLowerBoundary [] = 0ℚ
sumWeightedLowerBoundary (C ∷ rest) =
  weightedLowerBoundary C + sumWeightedLowerBoundary rest

sumWeightedUpperBoundary : List SignedCriticalShellCell → ℚ
sumWeightedUpperBoundary [] = 0ℚ
sumWeightedUpperBoundary (C ∷ rest) =
  weightedUpperBoundary C + sumWeightedUpperBoundary rest

finiteSignedCriticalLedgerExact :
  (cells : List SignedCriticalShellCell) →
  sumWeightedEnergyRate cells + sumWeightedDissipation cells
  ≡
  sumWeightedHH cells
  + sumWeightedLH cells
  + sumWeightedHL cells
  + sumWeightedCC cells
  + sumWeightedCom cells
  + sumWeightedLowerBoundary cells
  + sumWeightedUpperBoundary cells
finiteSignedCriticalLedgerExact [] = solve []
finiteSignedCriticalLedgerExact (C ∷ rest) =
  trans
    (solve
      ( weightedEnergyRate C
      ∷ weightedDissipation C
      ∷ sumWeightedEnergyRate rest
      ∷ sumWeightedDissipation rest
      ∷ []))
    (trans
      (cong₂ _+_
        (weightedShellBalance C)
        (finiteSignedCriticalLedgerExact rest))
      (solve
        ( weightedHH C ∷ weightedLH C ∷ weightedHL C ∷ weightedCC C
        ∷ weightedCom C ∷ weightedLowerBoundary C ∷ weightedUpperBoundary C
        ∷ sumWeightedHH rest ∷ sumWeightedLH rest ∷ sumWeightedHL rest
        ∷ sumWeightedCC rest ∷ sumWeightedCom rest
        ∷ sumWeightedLowerBoundary rest ∷ sumWeightedUpperBoundary rest
        ∷ [])))

------------------------------------------------------------------------
-- Mean-zero homogeneous carrier policy.
------------------------------------------------------------------------

record MeanZeroHomogeneousCriticalCarrier : Set where
  constructor mean-zero-homogeneous-critical-carrier
  field
    zeroModeExcluded : Bool
    zeroModeExcludedIsTrue : zeroModeExcluded ≡ true
    shellCells : List SignedCriticalShellCell

open MeanZeroHomogeneousCriticalCarrier public

meanZeroCarrierLedger :
  (carrier : MeanZeroHomogeneousCriticalCarrier) →
  sumWeightedEnergyRate (shellCells carrier)
    + sumWeightedDissipation (shellCells carrier)
  ≡
  sumWeightedHH (shellCells carrier)
    + sumWeightedLH (shellCells carrier)
    + sumWeightedHL (shellCells carrier)
    + sumWeightedCC (shellCells carrier)
    + sumWeightedCom (shellCells carrier)
    + sumWeightedLowerBoundary (shellCells carrier)
    + sumWeightedUpperBoundary (shellCells carrier)
meanZeroCarrierLedger carrier =
  finiteSignedCriticalLedgerExact (shellCells carrier)
