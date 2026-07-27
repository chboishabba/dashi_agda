module DASHI.Physics.Closure.NSTriadKNQuarticLyapunovDegreeAudit where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: David Darrow; Elizabeth Carlson; David Goluskin.
-- Title: "Quartic Lyapunov functions for global fluid stability".
-- Venue/year: arXiv preprint, 2026.
-- Journal DOI: none recorded on arXiv v1.
-- arXiv/DataCite DOI: 10.48550/arXiv.2606.18232.
-- arXiv: 2606.18232v1.
-- Uses: Remark 2.1 and equation (16).
-- Relationship: contrasts the valid square of Euler-invariant kinetic energy
-- with the DASHI-original positive-order H^s quintic obstruction.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as Nat
open import Relation.Binary.PropositionalEquality
  using (cong; subst; module ≡-Reasoning)

------------------------------------------------------------------------
-- Degree audit for transferring a quartic Lyapunov ansatz to the
-- homogeneous periodic H^s problem.
--
-- Darrow--Carlson--Goluskin square the ordinary kinetic energy.  Its
-- nonlinear derivative is zero, so no degree-five term is created.  A
-- positive-order H^s energy is different: its nonlinear derivative is
-- genuinely cubic.  Squaring that energy therefore creates a quintic term.
------------------------------------------------------------------------

record HsEvolutionScaling {s : Level} (State : Set s) : Set (lsuc s) where
  field
    scale : Nat → State → State
    hsEnergy hsNonlinear : State → Nat

    hsEnergyQuadratic : ∀ factor state →
      hsEnergy (scale factor state)
      ≡ (factor * factor) * hsEnergy state

    hsNonlinearCubic : ∀ factor state →
      hsNonlinear (scale factor state)
      ≡ (factor * factor) * (factor * hsNonlinear state)

open HsEvolutionScaling public

powerFour : Nat → Nat
powerFour factor = (factor * factor) * (factor * factor)

squaredHsNonlinear :
  ∀ {s} {State : Set s} →
  HsEvolutionScaling State → State → Nat
squaredHsNonlinear S state =
  hsEnergy S state * hsNonlinear S state

multiplyInterchange :
  ∀ a b c d →
  (a * b) * (c * d) ≡ (a * c) * (b * d)
multiplyInterchange a b c d =
  begin
    (a * b) * (c * d)
  ≡⟨ Nat.*-assoc a b (c * d) ⟩
    a * (b * (c * d))
  ≡⟨ cong (a *_) (Nat.*-assoc b c d ⟨) ⟩
    a * ((b * c) * d)
  ≡⟨ cong (λ middle → a * (middle * d)) (Nat.*-comm b c) ⟩
    a * ((c * b) * d)
  ≡⟨ cong (a *_) (Nat.*-assoc c b d) ⟩
    a * (c * (b * d))
  ≡⟨ Nat.*-assoc a c (b * d) ⟨
    (a * c) * (b * d)
  ∎
  where open ≡-Reasoning

moveFactorAcrossProduct :
  ∀ energyValue factor nonlinearValue →
  energyValue * (factor * nonlinearValue)
  ≡ factor * (energyValue * nonlinearValue)
moveFactorAcrossProduct energyValue factor nonlinearValue =
  begin
    energyValue * (factor * nonlinearValue)
  ≡⟨ Nat.*-assoc energyValue factor nonlinearValue ⟨
    (energyValue * factor) * nonlinearValue
  ≡⟨ cong (_* nonlinearValue) (Nat.*-comm energyValue factor) ⟩
    (factor * energyValue) * nonlinearValue
  ≡⟨ Nat.*-assoc factor energyValue nonlinearValue ⟩
    factor * (energyValue * nonlinearValue)
  ∎
  where open ≡-Reasoning

squaringHsEnergyCreatesDegreeFive :
  ∀ {s} {State : Set s}
    (S : HsEvolutionScaling State)
    (factor : Nat)
    (state : State) →
  squaredHsNonlinear S (scale S factor state)
  ≡
  powerFour factor * (factor * squaredHsNonlinear S state)
squaringHsEnergyCreatesDegreeFive S factor state
  rewrite hsEnergyQuadratic S factor state
        | hsNonlinearCubic S factor state
        | multiplyInterchange
            (factor * factor)
            (hsEnergy S state)
            (factor * factor)
            (factor * hsNonlinear S state)
        | moveFactorAcrossProduct
            (hsEnergy S state)
            factor
            (hsNonlinear S state)
  = refl

------------------------------------------------------------------------
-- A nonzero quintic term cannot be hidden inside one cutoff-independent
-- quartic bound.  This is the degree-five analogue of the existing
-- cubic-versus-quadratic obstruction.
------------------------------------------------------------------------

record QuinticQuarticScaling {s : Level} (State : Set s) : Set (lsuc s) where
  field
    scale : Nat → State → State
    quintic quartic : State → Nat

    quinticScaling : ∀ factor state →
      quintic (scale factor state)
      ≡ powerFour factor * (factor * quintic state)

    quarticScaling : ∀ factor state →
      quartic (scale factor state)
      ≡ powerFour factor * quartic state

open QuinticQuarticScaling public

rightFactorReassociate :
  ∀ constant fourthPower value →
  constant * (fourthPower * value)
  ≡ fourthPower * (constant * value)
rightFactorReassociate constant fourthPower value =
  begin
    constant * (fourthPower * value)
  ≡⟨ Nat.*-assoc constant fourthPower value ⟨
    (constant * fourthPower) * value
  ≡⟨ cong (_* value) (Nat.*-comm constant fourthPower) ⟩
    (fourthPower * constant) * value
  ≡⟨ Nat.*-assoc fourthPower constant value ⟩
    fourthPower * (constant * value)
  ∎
  where open ≡-Reasoning

uniformQuarticBoundAtScaleImpliesLinearBound :
  ∀ {s} {State : Set s}
    (S : QuinticQuarticScaling State)
    (constant : Nat)
    (uniformBound : ∀ state → quintic S state ≤ constant * quartic S state)
    (state : State)
    (predecessor : Nat) →
  suc predecessor * quintic S state
  ≤ constant * quartic S state
uniformQuarticBoundAtScaleImpliesLinearBound
    S constant uniformBound state predecessor =
  Nat.*-cancelˡ-≤ fourthPower factoredBound
  where
  factor : Nat
  factor = suc predecessor

  fourthPower : Nat
  fourthPower = powerFour factor

  scaledBound :
    fourthPower * (factor * quintic S state)
    ≤ constant * (fourthPower * quartic S state)
  scaledBound =
    subst
      (λ left → left ≤ constant * (fourthPower * quartic S state))
      (quinticScaling S factor state)
      (subst
        (λ right → quintic S (scale S factor state) ≤ constant * right)
        (quarticScaling S factor state)
        (uniformBound (scale S factor state)))

  factoredBound :
    fourthPower * (factor * quintic S state)
    ≤ fourthPower * (constant * quartic S state)
  factoredBound =
    subst
      (λ right →
        fourthPower * (factor * quintic S state) ≤ right)
      (rightFactorReassociate
        constant fourthPower (quartic S state))
      scaledBound

positiveQuinticWitnessRefutesUniformQuarticBound :
  ∀ {s} {State : Set s}
    (S : QuinticQuarticScaling State)
    (constant : Nat)
    (uniformBound : ∀ state → quintic S state ≤ constant * quartic S state)
    (state : State) →
  0 < quintic S state →
  ⊥
positiveQuinticWitnessRefutesUniformQuarticBound
    S constant uniformBound state quinticPositive =
  Nat.<⇒≱ strictGrowth cancelledBound
  where
  base : Nat
  base = constant * quartic S state

  factor : Nat
  factor = suc base

  factor≤factorTimesQuintic :
    factor ≤ factor * quintic S state
  factor≤factorTimesQuintic =
    subst
      (λ left → left ≤ factor * quintic S state)
      (Nat.*-identityʳ factor)
      (Nat.*-monoʳ-≤ factor quinticPositive)

  strictGrowth :
    constant * quartic S state
    < factor * quintic S state
  strictGrowth =
    Nat.<-≤-trans
      (Nat.n<1+n base)
      factor≤factorTimesQuintic

  cancelledBound :
    factor * quintic S state
    ≤ constant * quartic S state
  cancelledBound =
    uniformQuarticBoundAtScaleImpliesLinearBound
      S constant uniformBound state base

hsSquaredNonlinearAsQuintic :
  ∀ {s} {State : Set s}
    (S : HsEvolutionScaling State)
    (quarticControl : State → Nat)
    (quarticControlScaling : ∀ factor state →
      quarticControl (scale S factor state)
      ≡ powerFour factor * quarticControl state) →
  QuinticQuarticScaling State
hsSquaredNonlinearAsQuintic S quarticControl quarticControlScaling =
  record
    { scale = scale S
    ; quintic = squaredHsNonlinear S
    ; quartic = quarticControl
    ; quinticScaling = squaringHsEnergyCreatesDegreeFive S
    ; quarticScaling = quarticControlScaling
    }

quarticDegreeAuditClosed : Bool
quarticDegreeAuditClosed = true

quarticDegreeAuditClosedIsTrue :
  quarticDegreeAuditClosed ≡ true
quarticDegreeAuditClosedIsTrue = refl

bareHsSquareIsAQuarticClosure : Bool
bareHsSquareIsAQuarticClosure = false

bareHsSquareIsAQuarticClosureIsFalse :
  bareHsSquareIsAQuarticClosure ≡ false
bareHsSquareIsAQuarticClosureIsFalse = refl
