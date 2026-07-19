module DASHI.Cognition.ModeSelectionToProjectionLaw where

------------------------------------------------------------------------
-- A precise relational law from selected Turing pattern families to
-- possible Klüver projection classes.
--
-- The relation is deliberately partial and many-to-one.  It records a
-- projection possibility, not a deterministic forward model and not an
-- inverse reconstruction theorem.

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Biology.TuringPatternRegimeSurface using
  ( TuringPatternFamily
  ; frontFamily
  ; stripeFamily
  ; spotFamily
  ; hexagonFamily
  ; spiralFamily
  ; dissipativeSolitonFamily
  )
open import DASHI.Cognition.KlueverFormConstantProjection using
  ( KlueverForm
  ; latticeGrating
  ; tunnelFunnel
  ; spiral
  ; radialCobweb
  )
open import DASHI.Cognition.VisualTuringKlueverBridge using
  ( ProjectsAsKluever
  ; stripesAsLattice
  ; spotsAsLattice
  ; hexagonsAsLattice
  ; spiralAsSpiral
  ; frontAsTunnel
  ; frontAsRadial
  )

------------------------------------------------------------------------
-- Local empty type and inequality.

data ⊥ : Set where

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- Projection law: a selected family and a projection geometry determine a
-- set of admissible observed forms, represented by the bridge relation.

record ModeSelectionToProjectionLaw : Set₁ where
  constructor modeSelectionToProjectionLaw
  field
    selectedFamily : TuringPatternFamily
    observedForm : KlueverForm
    projectionWitness : ProjectsAsKluever selectedFamily observedForm

    projectionIsPossibleNotNecessary : Set
    projectionIsManyToOne : Set
    projectionIsNonTotal : Set
    noInverseCarrierRecovery : Set
    noSemanticPromotion : Set

------------------------------------------------------------------------
-- Concrete many-to-one witness: distinct selected families can project to
-- the same coarse lattice/grating form.

stripe≢spot : stripeFamily ≢ spotFamily
stripe≢spot ()

record ManyToOneLatticeWitness : Set where
  constructor manyToOneLatticeWitness
  field
    firstFamily : TuringPatternFamily
    secondFamily : TuringPatternFamily
    familiesDistinct : firstFamily ≢ secondFamily
    firstProjects : ProjectsAsKluever firstFamily latticeGrating
    secondProjects : ProjectsAsKluever secondFamily latticeGrating

canonicalManyToOneLatticeWitness : ManyToOneLatticeWitness
canonicalManyToOneLatticeWitness =
  manyToOneLatticeWitness
    stripeFamily
    spotFamily
    stripe≢spot
    stripesAsLattice
    spotsAsLattice

------------------------------------------------------------------------
-- Concrete non-totality witness: the current coarse relation intentionally
-- contains no constructor projecting the dissipative-soliton family.

noDissipativeSolitonProjection :
  ∀ form → ProjectsAsKluever dissipativeSolitonFamily form → ⊥
noDissipativeSolitonProjection form ()

record NonTotalProjectionWitness : Set₁ where
  constructor nonTotalProjectionWitness
  field
    omittedFamily : TuringPatternFamily
    noProjection : ∀ form → ProjectsAsKluever omittedFamily form → ⊥

canonicalNonTotalProjectionWitness : NonTotalProjectionWitness
canonicalNonTotalProjectionWitness =
  nonTotalProjectionWitness
    dissipativeSolitonFamily
    noDissipativeSolitonProjection

------------------------------------------------------------------------
-- Named admissible projection anchors.

stripeProjectionLaw : ModeSelectionToProjectionLaw
stripeProjectionLaw =
  modeSelectionToProjectionLaw
    stripeFamily
    latticeGrating
    stripesAsLattice
    ManyToOneLatticeWitness
    ManyToOneLatticeWitness
    NonTotalProjectionWitness
    ⊥
    ⊥

spiralProjectionLaw : ModeSelectionToProjectionLaw
spiralProjectionLaw =
  modeSelectionToProjectionLaw
    spiralFamily
    spiral
    spiralAsSpiral
    ProjectsAsKluever spiralFamily spiral
    ManyToOneLatticeWitness
    NonTotalProjectionWitness
    ⊥
    ⊥
