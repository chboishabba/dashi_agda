module DASHI.Moonshine.Monster3BCentralCharacterInertiaExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- R. W. Barraclough and R. A. Wilson,
-- "The Character Table of a Maximal Subgroup of the Monster",
-- LMS Journal of Computation and Mathematics 10 (2007), 161--175.
-- DOI: 10.1112/S1461157000001352.
--
-- I. M. Isaacs,
-- "Character Theory of Finite Groups",
-- Dover Publications, 1994 reprint of the 1976 edition.
-- ISBN: 978-0-486-68014-9; no DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Isolate the exact algebraic obstruction left by Round 4.  The full
-- normalizer may invert the central generator z and exchange the zeta and
-- zeta-squared eigensectors.  The inertia carrier consists of transformations
-- that preserve z; its action remains inside each chosen central-character
-- sector.  An inverting transformation is proved to swap the two sectors.
--
-- This is a proof-bearing generic construction.  It does not claim that the
-- actual Monster generators or their matrices have already been supplied.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; trans)

data CentralPhase3 : Set where
  phaseOne phaseZeta phaseZetaSquared : CentralPhase3

invertPhase : CentralPhase3 → CentralPhase3
invertPhase phaseOne = phaseOne
invertPhase phaseZeta = phaseZetaSquared
invertPhase phaseZetaSquared = phaseZeta

invertPhaseInvolutive :
  (phase : CentralPhase3) → invertPhase (invertPhase phase) ≡ phase
invertPhaseInvolutive phaseOne = refl
invertPhaseInvolutive phaseZeta = refl
invertPhaseInvolutive phaseZetaSquared = refl

zetaAndZetaSquaredDistinct : phaseZeta ≡ phaseZetaSquared → ⊥
zetaAndZetaSquaredDistinct ()

------------------------------------------------------------------------
-- A central operator, its inverse, and literal eigensectors.
------------------------------------------------------------------------

record CentralPhaseAction (State : Set) : Set₁ where
  field
    centralAct : State → State
    centralInverseAct : State → State
    phaseScale : CentralPhase3 → State → State
    inverseCentralOnEigenstate :
      (phase : CentralPhase3) →
      (state : State) →
      centralAct state ≡ phaseScale phase state →
      centralInverseAct state ≡ phaseScale (invertPhase phase) state

open CentralPhaseAction public

CentralEigenspace :
  ∀ {State} → CentralPhaseAction State → CentralPhase3 → Set
CentralEigenspace action phase =
  Σ _ (λ state → centralAct action state ≡ phaseScale action phase state)

stateOf :
  ∀ {State action phase} → CentralEigenspace {State} action phase → State
stateOf = proj₁

centralEigenlaw :
  ∀ {State action phase} →
  (eigenstate : CentralEigenspace {State} action phase) →
  centralAct action (stateOf eigenstate)
  ≡ phaseScale action phase (stateOf eigenstate)
centralEigenlaw = proj₂

------------------------------------------------------------------------
-- Transformations either preserve or invert the chosen central generator.
------------------------------------------------------------------------

record CentralNormalizerAction (State Normalizer : Set) : Set₁ where
  field
    phaseAction : CentralPhaseAction State
    act : Normalizer → State → State
    preservesOrInverts : Normalizer → Bool

    preservingIntertwiner :
      (normalizer : Normalizer) →
      preservesOrInverts normalizer ≡ true →
      (state : State) →
      centralAct phaseAction (act normalizer state)
      ≡ act normalizer (centralAct phaseAction state)

    invertingIntertwiner :
      (normalizer : Normalizer) →
      preservesOrInverts normalizer ≡ false →
      (state : State) →
      centralAct phaseAction (act normalizer state)
      ≡ act normalizer (centralInverseAct phaseAction state)

    phaseLinearity :
      (normalizer : Normalizer) →
      (phase : CentralPhase3) →
      (state : State) →
      act normalizer (phaseScale phaseAction phase state)
      ≡ phaseScale phaseAction phase (act normalizer state)

open CentralNormalizerAction public

CentralInertia : ∀ {State Normalizer} →
  CentralNormalizerAction State Normalizer → Set
CentralInertia action =
  Σ _ (λ normalizer → preservesOrInverts action normalizer ≡ true)

CentralInverter : ∀ {State Normalizer} →
  CentralNormalizerAction State Normalizer → Set
CentralInverter action =
  Σ _ (λ normalizer → preservesOrInverts action normalizer ≡ false)

inertiaActsWithinPhase :
  ∀ {State Normalizer}
    (normalizerAction : CentralNormalizerAction State Normalizer) →
    (phase : CentralPhase3) →
    CentralInertia normalizerAction →
    CentralEigenspace (phaseAction normalizerAction) phase →
    CentralEigenspace (phaseAction normalizerAction) phase
inertiaActsWithinPhase normalizerAction phase (normalizer , preserves) (state , eigenlaw) =
  act normalizerAction normalizer state ,
  trans
    (preservingIntertwiner normalizerAction normalizer preserves state)
    (trans
      (cong (act normalizerAction normalizer) eigenlaw)
      (phaseLinearity normalizerAction normalizer phase state))

inertiaPreservesZetaSector :
  ∀ {State Normalizer}
    (normalizerAction : CentralNormalizerAction State Normalizer) →
    CentralInertia normalizerAction →
    CentralEigenspace (phaseAction normalizerAction) phaseZeta →
    CentralEigenspace (phaseAction normalizerAction) phaseZeta
inertiaPreservesZetaSector normalizerAction =
  inertiaActsWithinPhase normalizerAction phaseZeta

inverterSwapsPhase :
  ∀ {State Normalizer}
    (normalizerAction : CentralNormalizerAction State Normalizer) →
    (phase : CentralPhase3) →
    CentralInverter normalizerAction →
    CentralEigenspace (phaseAction normalizerAction) phase →
    CentralEigenspace
      (phaseAction normalizerAction)
      (invertPhase phase)
inverterSwapsPhase normalizerAction phase (normalizer , inverts) (state , eigenlaw) =
  act normalizerAction normalizer state ,
  trans
    (invertingIntertwiner normalizerAction normalizer inverts state)
    (trans
      (cong (act normalizerAction normalizer)
        (inverseCentralOnEigenstate
          (phaseAction normalizerAction) phase state eigenlaw))
      (phaseLinearity normalizerAction normalizer (invertPhase phase) state))

inverterSendsZetaToZetaSquared :
  ∀ {State Normalizer}
    (normalizerAction : CentralNormalizerAction State Normalizer) →
    CentralInverter normalizerAction →
    CentralEigenspace (phaseAction normalizerAction) phaseZeta →
    CentralEigenspace (phaseAction normalizerAction) phaseZetaSquared
inverterSendsZetaToZetaSquared normalizerAction =
  inverterSwapsPhase normalizerAction phaseZeta

inverterSendsZetaSquaredToZeta :
  ∀ {State Normalizer}
    (normalizerAction : CentralNormalizerAction State Normalizer) →
    CentralInverter normalizerAction →
    CentralEigenspace (phaseAction normalizerAction) phaseZetaSquared →
    CentralEigenspace (phaseAction normalizerAction) phaseZeta
inverterSendsZetaSquaredToZeta normalizerAction =
  inverterSwapsPhase normalizerAction phaseZetaSquared

record ActualMonster3BPhaseResolvedSector : Set₁ where
  field
    State Normalizer : Set
    normalizerAction : CentralNormalizerAction State Normalizer
    chosenZetaSector : Set
    includeChosenZeta :
      chosenZetaSector →
      CentralEigenspace (phaseAction normalizerAction) phaseZeta
    recoverChosenZeta :
      CentralEigenspace (phaseAction normalizerAction) phaseZeta →
      chosenZetaSector
    recoverAfterInclude :
      (state : chosenZetaSector) →
      recoverChosenZeta (includeChosenZeta state) ≡ state
    includeAfterRecover :
      (state : CentralEigenspace (phaseAction normalizerAction) phaseZeta) →
      includeChosenZeta (recoverChosenZeta state) ≡ state

record CentralCharacterInertiaBoundary : Set where
  constructor central-character-inertia-boundary
  field
    inertiaPreservationProved : Bool
    inertiaPreservationProvedIsTrue : inertiaPreservationProved ≡ true
    inversionSwapProved : Bool
    inversionSwapProvedIsTrue : inversionSwapProved ≡ true
    actualMonsterPhaseResolvedSectorConstructed : Bool
    actualMonsterPhaseResolvedSectorConstructedIsFalse :
      actualMonsterPhaseResolvedSectorConstructed ≡ false
    actualInertiaGeneratorMatricesConstructed : Bool
    actualInertiaGeneratorMatricesConstructedIsFalse :
      actualInertiaGeneratorMatricesConstructed ≡ false

canonicalCentralCharacterInertiaBoundary : CentralCharacterInertiaBoundary
canonicalCentralCharacterInertiaBoundary =
  central-character-inertia-boundary true refl true refl false refl false refl
