{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345CanonicalStateRound838Exact where

------------------------------------------------------------------------
-- R838 / ACTUAL ROUND71 CANONICAL RADIUS-FOUR STATE FOR THE 3-4-5 WITNESS
--
-- Populate EVERY canonical positive reality-orbit slot at cutoff four with
-- Snapshot.velocity345.  Hence the state is a genuine Round71 finite reality
-- state, not a six-mode surrogate.  All unused slots store literal zero.
--
-- The only nonzero positive representatives are
--   (0,4,0), (3,0,0), (3,4,0).
-- Their transversality is proved exactly over an arbitrary rational
-- IntegerEmbedding; the negative sheet is reconstructed by existing Round71
-- reality lookup.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNCanonicalRealityOrbitHalfLatticeRound63Exact as Half
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffOrbitCarrierRound63Exact as Orbit
import DASHI.Physics.Closure.NSTriadKNFixedCanonicalRealityVectorFieldRound71Exact as Fixed
import DASHI.Physics.Closure.NSTriadKNFixedCanonicalRealityLookupExactRound71Exact as Lookup
import DASHI.Physics.Closure.NSTriadKNFixedCanonicalTransverseInvariantRound71Exact as Transverse
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityTransverseRound30Exact as R30
import DASHI.Physics.Closure.NSTriadKNRationalIntegerEmbeddingModeNormScaleExact as Scale
import DASHI.Physics.Closure.NSTriadKNR650Rational345ActiveHelicalScalarsRound835Exact as Active
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSnapshotRound836Exact as Snapshot

F : C3.RealField _
F = Rational.rationalRealField

snapshotPositiveValues :
  List Z3.FourierMode → List (Fixed.CanonicalModeValue F)
snapshotPositiveValues [] = []
snapshotPositiveValues (mode ∷ rest) =
  Fixed.canonical-mode-value mode (Snapshot.velocity345 mode)
  ∷ snapshotPositiveValues rest

snapshotPositiveModesExact :
  (modes : List Z3.FourierMode) →
  Fixed.modeList (snapshotPositiveValues modes) ≡ modes
snapshotPositiveModesExact [] = refl
snapshotPositiveModesExact (mode ∷ rest)
  rewrite snapshotPositiveModesExact rest = refl

canonicalSnapshotState : Fixed.CanonicalRealityState F 4
canonicalSnapshotState =
  Fixed.canonical-reality-state
    (snapshotPositiveValues (Orbit.canonicalCutoffOrbitModes 4))
    (snapshotPositiveModesExact (Orbit.canonicalCutoffOrbitModes 4))

snapshotEntryMember :
  ∀ {mode modes} →
  mode Cube.∈ modes →
  Fixed.canonical-mode-value mode (Snapshot.velocity345 mode)
    Cube.∈ snapshotPositiveValues modes
snapshotEntryMember (Cube.here refl) = Cube.here refl
snapshotEntryMember (Cube.there member) =
  Cube.there (snapshotEntryMember member)

positiveVelocityExact :
  (mode : Z3.FourierMode) →
  mode Cube.∈ Orbit.canonicalCutoffOrbitModes 4 →
  Fixed.realityVelocity canonicalSnapshotState mode
  ≡ Snapshot.velocity345 mode
positiveVelocityExact mode member =
  Lookup.realityVelocityPositiveExact
    canonicalSnapshotState
    (Fixed.canonical-mode-value mode (Snapshot.velocity345 mode))
    (snapshotEntryMember member)

------------------------------------------------------------------------
-- Exact active-support classification.
------------------------------------------------------------------------

data VelocityActiveHit (mode : Z3.FourierMode) : Set where
  hit₁ : mode ≡ Active.k₁ → VelocityActiveHit mode
  hit₂ : mode ≡ Active.k₂ → VelocityActiveHit mode
  hit₄ : mode ≡ Active.k₄ → VelocityActiveHit mode
  hit₅ : mode ≡ Active.k₅ → VelocityActiveHit mode
  hit₇ : mode ≡ Active.k₇ → VelocityActiveHit mode
  hit₈ : mode ≡ Active.k₈ → VelocityActiveHit mode

velocityActiveSound :
  (mode : Z3.FourierMode) →
  Snapshot.velocityActive mode ≡ true →
  VelocityActiveHit mode
velocityActiveSound mode active
  with Output.modeEqual mode Active.k₁ in d₁
... | true = hit₁ (Output.modeEqualSound d₁)
... | false
  with Output.modeEqual mode Active.k₂ in d₂
... | true = hit₂ (Output.modeEqualSound d₂)
... | false
  with Output.modeEqual mode Active.k₄ in d₄
... | true = hit₄ (Output.modeEqualSound d₄)
... | false
  with Output.modeEqual mode Active.k₅ in d₅
... | true = hit₅ (Output.modeEqualSound d₅)
... | false
  with Output.modeEqual mode Active.k₇ in d₇
... | true = hit₇ (Output.modeEqualSound d₇)
... | false
  with Output.modeEqual mode Active.k₈ in d₈
... | true = hit₈ (Output.modeEqualSound d₈)
... | false = Output.falseNotTrue active

------------------------------------------------------------------------
-- Three nonzero positive modes are transverse for ANY additive rational
-- integer embedding.  No unit-normalization assumption is needed.
------------------------------------------------------------------------

k₅Transverse :
  (E : C3.IntegerEmbedding F) →
  C3.bilinearDot3
    (C3.modeVector E Active.k₅)
    (Snapshot.velocity345 Active.k₅)
  ≡ C3.complexZero F
k₅Transverse E
  rewrite C3.embedZero E =
  Algebra.complexExt
    (solve (C3.embedInteger E (Z3.ky Active.k₅) ∷ []))
    (solve (C3.embedInteger E (Z3.ky Active.k₅) ∷ []))

k₇Transverse :
  (E : C3.IntegerEmbedding F) →
  C3.bilinearDot3
    (C3.modeVector E Active.k₇)
    (Snapshot.velocity345 Active.k₇)
  ≡ C3.complexZero F
k₇Transverse E
  rewrite C3.embedZero E =
  Algebra.complexExt
    (solve (C3.embedInteger E (Z3.kx Active.k₇) ∷ []))
    (solve (C3.embedInteger E (Z3.kx Active.k₇) ∷ []))

k₈Transverse :
  (E : C3.IntegerEmbedding F) →
  C3.bilinearDot3
    (C3.modeVector E Active.k₈)
    (Snapshot.velocity345 Active.k₈)
  ≡ C3.complexZero F
k₈Transverse E
  rewrite Scale.positiveNatEmbeddingScale E 3
        | Scale.positiveNatEmbeddingScale E 4
        | C3.embedZero E =
  Algebra.complexExt
    (solve (Scale.embeddingUnit E ∷ []))
    (solve (Scale.embeddingUnit E ∷ []))

snapshotVelocityTransverseOnPositive :
  (E : C3.IntegerEmbedding F) →
  (mode : Z3.FourierMode) →
  Half.leadingPositive mode ≡ true →
  C3.bilinearDot3
    (C3.modeVector E mode)
    (Snapshot.velocity345 mode)
  ≡ C3.complexZero F
snapshotVelocityTransverseOnPositive E mode positive
  with Snapshot.velocityActive mode in active
... | false =
  trans
    (cong (C3.bilinearDot3 (C3.modeVector E mode))
      (Snapshot.velocityInactiveZero mode active))
    (R30.bilinearDot3ZeroRight (C3.modeVector E mode))
... | true with velocityActiveSound mode active
...   | hit₁ same =
      Output.falseNotTrue
        (subst (λ selected → Half.leadingPositive selected ≡ true)
          same positive)
...   | hit₂ same =
      Output.falseNotTrue
        (subst (λ selected → Half.leadingPositive selected ≡ true)
          same positive)
...   | hit₄ same =
      Output.falseNotTrue
        (subst (λ selected → Half.leadingPositive selected ≡ true)
          same positive)
...   | hit₅ same =
      subst
        (λ selected →
          C3.bilinearDot3
            (C3.modeVector E selected)
            (Snapshot.velocity345 selected)
          ≡ C3.complexZero F)
        (sym same)
        (k₅Transverse E)
...   | hit₇ same =
      subst
        (λ selected →
          C3.bilinearDot3
            (C3.modeVector E selected)
            (Snapshot.velocity345 selected)
          ≡ C3.complexZero F)
        (sym same)
        (k₇Transverse E)
...   | hit₈ same =
      subst
        (λ selected →
          C3.bilinearDot3
            (C3.modeVector E selected)
            (Snapshot.velocity345 selected)
          ≡ C3.complexZero F)
        (sym same)
        (k₈Transverse E)

geometry345 :
  (E : C3.IntegerEmbedding F) →
  C3.ModeInverseSquare F E →
  Fixed.FixedCanonicalGeometry F E
geometry345 E I =
  Fixed.fixed-canonical-geometry 4 I 1

canonicalSnapshotPositiveTransverse :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  Transverse.CanonicalPositiveTransverse
    (geometry345 E I) canonicalSnapshotState
canonicalSnapshotPositiveTransverse E I mode member =
  trans
    (cong (C3.bilinearDot3 (C3.modeVector E mode))
      (positiveVelocityExact mode member))
    (snapshotVelocityTransverseOnPositive E mode
      (Orbit.canonicalCutoffMemberPositive member))

round838ActualRound71RadiusFourStateConstructed : Bool
round838ActualRound71RadiusFourStateConstructed = true

round838AllCanonicalPositiveSlotsPopulated : Bool
round838AllCanonicalPositiveSlotsPopulated = true

round838SparseInitialStatePositiveTransverse : Bool
round838SparseInitialStatePositiveTransverse = true

round838NegativeRealitySheetProvidedByRound71 : Bool
round838NegativeRealitySheetProvidedByRound71 = true

round838ProjectedNonlinearityRowsEvaluated : Bool
round838ProjectedNonlinearityRowsEvaluated = false

round838RealPicardApplied : Bool
round838RealPicardApplied = false

round838ClayPromotion : Bool
round838ClayPromotion = false

round838ActualRound71RadiusFourStateConstructedIsTrue :
  round838ActualRound71RadiusFourStateConstructed ≡ true
round838ActualRound71RadiusFourStateConstructedIsTrue = refl
