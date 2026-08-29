module DASHI.Biology.CyclotomicPhaseAmplitudeBoundaryExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic

------------------------------------------------------------------------
-- Finite observable shadow of Aristotle's cyclotomic C3 owner:
--   Lean/Spine/TernaryPhase.lean
--
-- The archive proves zeta^3 = 1, conjugate(zeta) = zeta^2 and separates the
-- fixed real sector from the nontrivial phase sector.  Here we retain the exact
-- finite phase/conjugation structure and explicitly add amplitude as an
-- independent coordinate.  No continuous scalar field is manufactured from
-- three phase labels alone.

data C3Phase : Set where
  phaseOne : C3Phase
  phaseZeta : C3Phase
  phaseZetaSquared : C3Phase

phaseAdvance : C3Phase → C3Phase
phaseAdvance phaseOne = phaseZeta
phaseAdvance phaseZeta = phaseZetaSquared
phaseAdvance phaseZetaSquared = phaseOne

phaseAdvanceCube :
  (p : C3Phase) →
  phaseAdvance (phaseAdvance (phaseAdvance p)) ≡ p
phaseAdvanceCube phaseOne = refl
phaseAdvanceCube phaseZeta = refl
phaseAdvanceCube phaseZetaSquared = refl

conjugatePhase : C3Phase → C3Phase
conjugatePhase phaseOne = phaseOne
conjugatePhase phaseZeta = phaseZetaSquared
conjugatePhase phaseZetaSquared = phaseZeta

conjugatePhaseInvolutive :
  (p : C3Phase) → conjugatePhase (conjugatePhase p) ≡ p
conjugatePhaseInvolutive phaseOne = refl
conjugatePhaseInvolutive phaseZeta = refl
conjugatePhaseInvolutive phaseZetaSquared = refl

phaseOneFixedByConjugation :
  conjugatePhase phaseOne ≡ phaseOne
phaseOneFixedByConjugation = refl

zetaNotFixedByConjugation :
  conjugatePhase phaseZeta ≡ phaseZeta → ⊥
zetaNotFixedByConjugation ()

zetaSquaredNotFixedByConjugation :
  conjugatePhase phaseZetaSquared ≡ phaseZetaSquared → ⊥
zetaSquaredNotFixedByConjugation ()

phaseNormCode : C3Phase → Nat
phaseNormCode phaseOne = 1
phaseNormCode phaseZeta = 1
phaseNormCode phaseZetaSquared = 1

allUnitPhasesHaveNormOne :
  (p : C3Phase) → phaseNormCode p ≡ 1
allUnitPhasesHaveNormOne phaseOne = refl
allUnitPhasesHaveNormOne phaseZeta = refl
allUnitPhasesHaveNormOne phaseZetaSquared = refl

tritPhase : Triadic.KernelTrit → C3Phase
tritPhase Triadic.zeroTrit = phaseOne
tritPhase Triadic.positiveTrit = phaseZeta
tritPhase Triadic.negativeTrit = phaseZetaSquared

------------------------------------------------------------------------
-- Quantitative strength is independent from phase.

record AmplitudePhaseState : Set where
  constructor amplitudePhaseState
  field
    amplitude : Nat
    phase : C3Phase

open AmplitudePhaseState public

samePhaseDifferentAmplitudeA : AmplitudePhaseState
samePhaseDifferentAmplitudeA = amplitudePhaseState 1 phaseZeta

samePhaseDifferentAmplitudeB : AmplitudePhaseState
samePhaseDifferentAmplitudeB = amplitudePhaseState 4 phaseZeta

samePhaseWitness :
  phase samePhaseDifferentAmplitudeA ≡ phase samePhaseDifferentAmplitudeB
samePhaseWitness = refl

differentAmplitudeWitness :
  amplitude samePhaseDifferentAmplitudeA
  ≡ amplitude samePhaseDifferentAmplitudeB → ⊥
differentAmplitudeWitness ()

sameAmplitudeDifferentPhaseA : AmplitudePhaseState
sameAmplitudeDifferentPhaseA = amplitudePhaseState 2 phaseZeta

sameAmplitudeDifferentPhaseB : AmplitudePhaseState
sameAmplitudeDifferentPhaseB = amplitudePhaseState 2 phaseZetaSquared

sameAmplitudeWitness :
  amplitude sameAmplitudeDifferentPhaseA
  ≡ amplitude sameAmplitudeDifferentPhaseB
sameAmplitudeWitness = refl

differentPhaseWitness :
  phase sameAmplitudeDifferentPhaseA
  ≡ phase sameAmplitudeDifferentPhaseB → ⊥
differentPhaseWitness ()

record CyclotomicPhaseBoundary : Set where
  constructor cyclotomicPhaseBoundary
  field
    threePhaseLabelsSupplyContinuousAmplitude : Bool
    threePhaseLabelsSupplyContinuousAmplitudeIsFalse :
      threePhaseLabelsSupplyContinuousAmplitude ≡ false

    equalNormCodeIdentifiesPhase : Bool
    equalNormCodeIdentifiesPhaseIsFalse :
      equalNormCodeIdentifiesPhase ≡ false

canonicalCyclotomicPhaseBoundary : CyclotomicPhaseBoundary
canonicalCyclotomicPhaseBoundary =
  cyclotomicPhaseBoundary false refl false refl
