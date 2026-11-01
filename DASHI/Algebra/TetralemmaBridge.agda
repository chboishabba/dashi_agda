module DASHI.Algebra.TetralemmaBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Agda.Builtin.String using (String)

open import Base369 using
  ( TriTruth
  ; tri-low ; tri-mid ; tri-high
  )
open import LogicTlurey using
  ( Stage
  ; seed ; counter ; resonance ; overflow
  ; stageTone
  )
open import DASHI.Interop.SensibLawResidualLattice using
  ( ResidualLevel
  ; exact ; partial ; noTypedMeet ; contradiction
  )

------------------------------------------------------------------------
-- Tetralemma alignment surface.
--
-- The bridge records a shared four-position vocabulary for LogicTlurey stages
-- and SensibLaw residual levels.  It does not assert historical, religious, or
-- semantic equivalence; it is a formal alignment carrier only.

data TetralemmaPosition : Set where
  affirmation : TetralemmaPosition
  negation : TetralemmaPosition
  both : TetralemmaPosition
  neither : TetralemmaPosition

stageTetralemma : Stage → TetralemmaPosition
stageTetralemma seed = affirmation
stageTetralemma counter = negation
stageTetralemma resonance = both
stageTetralemma overflow = neither

tetralemmaTone : TetralemmaPosition → TriTruth
tetralemmaTone affirmation = tri-low
tetralemmaTone negation = tri-mid
tetralemmaTone both = tri-high
tetralemmaTone neither = tri-low

stageTone-via-tetralemma :
  ∀ s →
  stageTone s ≡ tetralemmaTone (stageTetralemma s)
stageTone-via-tetralemma seed = refl
stageTone-via-tetralemma counter = refl
stageTone-via-tetralemma resonance = refl
stageTone-via-tetralemma overflow = refl

residualTetralemma : ResidualLevel → TetralemmaPosition
residualTetralemma exact = affirmation
residualTetralemma partial = both
residualTetralemma noTypedMeet = neither
residualTetralemma contradiction = negation

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

triResidual : TriTruth → ResidualLevel
triResidual tri-low = exact
triResidual tri-mid = partial
triResidual tri-high = noTypedMeet

stageResidualTone : Stage → ResidualLevel
stageResidualTone s = triResidual (stageTone s)

triResidual-low : triResidual tri-low ≡ exact
triResidual-low = refl

triResidual-mid : triResidual tri-mid ≡ partial
triResidual-mid = refl

triResidual-high : triResidual tri-high ≡ noTypedMeet
triResidual-high = refl

triResidual-excludes-contradiction :
  ∀ t →
  triResidual t ≢ contradiction
triResidual-excludes-contradiction tri-low ()
triResidual-excludes-contradiction tri-mid ()
triResidual-excludes-contradiction tri-high ()

stageResidualTone-excludes-contradiction :
  ∀ s →
  stageResidualTone s ≢ contradiction
stageResidualTone-excludes-contradiction seed ()
stageResidualTone-excludes-contradiction counter ()
stageResidualTone-excludes-contradiction resonance ()
stageResidualTone-excludes-contradiction overflow ()

exact-is-affirmation : residualTetralemma exact ≡ affirmation
exact-is-affirmation = refl

partial-is-both : residualTetralemma partial ≡ both
partial-is-both = refl

noTypedMeet-is-neither : residualTetralemma noTypedMeet ≡ neither
noTypedMeet-is-neither = refl

contradiction-is-negation : residualTetralemma contradiction ≡ negation
contradiction-is-negation = refl

record TetralemmaBridgeSurface : Set₁ where
  field
    positionCarrier : Set
    stageProjection : Stage → TetralemmaPosition
    residualProjection : ResidualLevel → TetralemmaPosition
    toneResidualProjection : TriTruth → ResidualLevel
    stageToneFactors :
      ∀ s →
      stageTone s ≡ tetralemmaTone (stageProjection s)
    toneResidualExcludesContradiction :
      ∀ t →
      toneResidualProjection t ≢ contradiction
    nonClaimBoundary : List String

tetralemmaBridgeSurface : TetralemmaBridgeSurface
tetralemmaBridgeSurface =
  record
    { positionCarrier = TetralemmaPosition
    ; stageProjection = stageTetralemma
    ; residualProjection = residualTetralemma
    ; toneResidualProjection = triResidual
    ; stageToneFactors = stageTone-via-tetralemma
    ; toneResidualExcludesContradiction = triResidual-excludes-contradiction
    ; nonClaimBoundary =
        "LogicTlurey stage cycle and SensibLaw residual chain share a four-position carrier only"
        ∷ "The Stage topology is cyclic; the ResidualLevel topology is an ordered join-semilattice"
        ∷ "TriTruth tone embeds only into exact/partial/noTypedMeet; contradiction is cross-claim pressure"
        ∷ "The bridge does not identify runtime PNF evidence with dialectical truth"
        ∷ []
    }
