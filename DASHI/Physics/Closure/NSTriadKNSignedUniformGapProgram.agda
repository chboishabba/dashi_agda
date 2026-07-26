module DASHI.Physics.Closure.NSTriadKNSignedUniformGapProgram where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_; _-_)
open import Data.Nat.Base using (_≤_; _<_)

import DASHI.Physics.Closure.NSTriadKNCutoffUniformClasswiseEstimateProgram as Classwise

------------------------------------------------------------------------
-- Exact signed operator and its symmetric part.
------------------------------------------------------------------------

record SignedOperatorData {c s q : Level} : Set (lsuc (c ⊔ s ⊔ q)) where
  field
    Cutoff : Set c
    State : Set s
    SignedScalar : Set q

    operator : Cutoff → State → State
    adjointOperator : Cutoff → State → State
    symmetricPart : Cutoff → State → State

    signedPairing : Cutoff → State → State → SignedScalar
    signedQuadratic : Cutoff → State → SignedScalar

    symmetricPartMeaning : ∀ N state →
      signedQuadratic N state
      ≡ signedPairing N state (symmetricPart N state)

    skewPartCancelsInQuadraticForm : Set

open SignedOperatorData public

------------------------------------------------------------------------
-- Route A: positive majorant.
------------------------------------------------------------------------

record PositiveMajorantGapRoute
    {c s q : Level}
    (data : SignedOperatorData {c} {s} {q}) : Set (lsuc (c ⊔ s ⊔ q)) where
  field
    magnitude : SignedScalar data → Nat
    majorantQuadratic baseQuadratic strongNormSquared :
      Cutoff data → State data → Nat
    scaleSquare : Cutoff data → Nat

    exactSignedBelowMajorant : ∀ N state →
      magnitude (signedQuadratic data N state)
      ≤ majorantQuadratic N state

    majorantConstant baseConstant : Nat

    majorantUniform : ∀ N state →
      scaleSquare N * majorantQuadratic N state
      ≤ majorantConstant * strongNormSquared N state

    baseCoercive : ∀ N state →
      baseConstant * strongNormSquared N state
      ≤ scaleSquare N * baseQuadratic N state

    strictMajorantGap : majorantConstant < baseConstant

open PositiveMajorantGapRoute public

------------------------------------------------------------------------
-- Route B: preserve signed blocks and estimate only the symmetric part.
------------------------------------------------------------------------

record SignedBlockGapRoute
    {c s q : Level}
    (data : SignedOperatorData {c} {s} {q}) : Set (lsuc (c ⊔ s ⊔ q)) where
  field
    blockIndex : Set
    blockOperator :
      blockIndex → Cutoff data → State data → State data

    blockDecompositionExact : Set
    permutationCancellationExact : Set
    realityOrbitCancellationExact : Set
    completeTriadCancellationExact : Set

    numericalRangeMagnitude :
      Cutoff data → State data → Nat
    strongNormSquared baseQuadratic scaleSquare :
      Cutoff data → State data → Nat

    signedConstant baseConstant : Nat

    symmetricNumericalRangeUniform : ∀ N state →
      scaleSquare N state * numericalRangeMagnitude N state
      ≤ signedConstant * strongNormSquared N state

    baseCoercive : ∀ N state →
      baseConstant * strongNormSquared N state
      ≤ scaleSquare N state * baseQuadratic N state

    strictSignedGap : signedConstant < baseConstant

open SignedBlockGapRoute public

------------------------------------------------------------------------
-- Route C: modified energy with cross-shell correction.
------------------------------------------------------------------------

record ModifiedEnergyGapRoute
    {c s q : Level}
    (data : SignedOperatorData {c} {s} {q}) : Set (lsuc (c ⊔ s ⊔ q)) where
  field
    diagonalEnergy crossShellCorrection modifiedEnergy :
      Cutoff data → State data → Nat

    modifiedEnergyMeaning : ∀ N state →
      modifiedEnergy N state
      ≡ diagonalEnergy N state + crossShellCorrection N state

    lowerEquivalenceConstant upperEquivalenceConstant : Nat
    lowerEnergyEquivalence : ∀ N state →
      lowerEquivalenceConstant * diagonalEnergy N state
      ≤ modifiedEnergy N state
    upperEnergyEquivalence : ∀ N state →
      modifiedEnergy N state
      ≤ upperEquivalenceConstant * diagonalEnergy N state

    dissipation nonlinearRemainder : Cutoff data → State data → Nat
    derivativeControlled : Set

    absorptionConstant dissipationConstant : Nat
    nonlinearAbsorbed : ∀ N state →
      nonlinearRemainder N state
      ≤ absorptionConstant * dissipation N state
    strictAbsorption : absorptionConstant < dissipationConstant

open ModifiedEnergyGapRoute public

------------------------------------------------------------------------
-- Uniform conclusion shared by all routes.
------------------------------------------------------------------------

record UniformSignedSpectralGap
    {c s : Level} : Set (lsuc (c ⊔ s)) where
  field
    Cutoff : Set c
    State : Set s

    scaleSquare : Cutoff → Nat
    qBase qError strongNormSquared : Cutoff → State → Nat

    baseConstant errorConstant delta : Nat

    deltaMeaning : delta ≡ baseConstant - errorConstant
    deltaPositive : 0 < delta

    baseCoercive : ∀ N state →
      baseConstant * strongNormSquared N state
      ≤ scaleSquare N * qBase N state

    errorControlled : ∀ N state →
      scaleSquare N * qError N state
      ≤ errorConstant * strongNormSquared N state

    strictGap : errorConstant < baseConstant
    exactPhysicalSignedOperatorUsed : Set
    appliesToEveryAdmissibleState : Set

open UniformSignedSpectralGap public

data GapRouteSelected : Set where
  viaPositiveMajorant viaSignedBlocks viaModifiedEnergy : GapRouteSelected

record UniformGapPromotion : Set₁ where
  field
    selectedRoute : GapRouteSelected
    gap : UniformSignedSpectralGap
    finiteExperimentsUsedOnlyForFalsification : Set
    noFiniteToUniformPromotion : Set
    noPositivePartEqualityAssumed : Set

open UniformGapPromotion public

threeUniformGapRoutesImplemented : Bool
threeUniformGapRoutesImplemented = true

threeUniformGapRoutesImplementedIsTrue :
  threeUniformGapRoutesImplemented ≡ true
threeUniformGapRoutesImplementedIsTrue = refl

strictCutoffUniformSignedGapClosed : Bool
strictCutoffUniformSignedGapClosed = false

strictCutoffUniformSignedGapClosedIsFalse :
  strictCutoffUniformSignedGapClosed ≡ false
strictCutoffUniformSignedGapClosedIsFalse = refl
