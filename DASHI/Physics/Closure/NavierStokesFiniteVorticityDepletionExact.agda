module DASHI.Physics.Closure.NavierStokesFiniteVorticityDepletionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Peter Constantin and Charles Fefferman,
-- "Direction of Vorticity and the Problem of Global Regularity for the
-- Navier-Stokes Equations",
-- Indiana University Mathematics Journal 42 (1993), 775--789.
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- DASHI CONTRIBUTION
--
-- Prove a finite interaction version of geometric depletion.  Each stretching
-- contribution is bounded by
--
--   angle-defect * kernel-weight * vorticity-amplitude,
--
-- and a common coherence bound on the angle defect contracts that term.
-- Pointwise contraction is propagated through an arbitrary finite sum.
--
-- This is a genuine finite inequality, not a continuum regularity theorem.
-- Constructing the Biot--Savart interaction family, obtaining a Hölder
-- coherence modulus from the vorticity direction, controlling singular
-- kernels and feeding the estimate into BKM remain explicit analytic steps.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; _+_; _*_)
open import Agda.Builtin.Bool using (false)
open import Data.Nat.Base using (_≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-mono-≤; *-mono-≤)
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSVorticityStretchingExactReceipt as Existing

record FiniteStretchingInteraction (coherenceBound : Nat) : Set where
  constructor stretchingInteraction
  field
    rawStretching : Nat
    angleDefect : Nat
    kernelWeight : Nat
    vorticityAmplitude : Nat

    stretchingKernelBound :
      rawStretching
      ≤ (angleDefect * kernelWeight) * vorticityAmplitude

    coherenceControlsAngle : angleDefect ≤ coherenceBound

open FiniteStretchingInteraction public

controlledContribution :
  ∀ {coherenceBound} →
  FiniteStretchingInteraction coherenceBound → Nat
controlledContribution {coherenceBound} interaction =
  (coherenceBound * kernelWeight interaction)
    * vorticityAmplitude interaction

pointwiseGeometricDepletion :
  ∀ {coherenceBound}
    (interaction : FiniteStretchingInteraction coherenceBound) →
  rawStretching interaction ≤ controlledContribution interaction
pointwiseGeometricDepletion {coherenceBound} interaction =
  ≤-trans
    (stretchingKernelBound interaction)
    (*-mono-≤
      (*-mono-≤ (coherenceControlsAngle interaction) ≤-refl)
      ≤-refl)

sumRawStretching :
  ∀ {coherenceBound} →
  List (FiniteStretchingInteraction coherenceBound) → Nat
sumRawStretching [] = zero
sumRawStretching (interaction ∷ interactions) =
  rawStretching interaction + sumRawStretching interactions

sumControlledStretching :
  ∀ {coherenceBound} →
  List (FiniteStretchingInteraction coherenceBound) → Nat
sumControlledStretching [] = zero
sumControlledStretching (interaction ∷ interactions) =
  controlledContribution interaction
    + sumControlledStretching interactions

finiteSumGeometricDepletion :
  ∀ {coherenceBound}
    (interactions : List (FiniteStretchingInteraction coherenceBound)) →
  sumRawStretching interactions ≤ sumControlledStretching interactions
finiteSumGeometricDepletion [] = ≤-refl
finiteSumGeometricDepletion (interaction ∷ interactions) =
  +-mono-≤
    (pointwiseGeometricDepletion interaction)
    (finiteSumGeometricDepletion interactions)

------------------------------------------------------------------------
-- Concrete nontrivial two-interaction certificate.
------------------------------------------------------------------------

firstInteraction : FiniteStretchingInteraction 2
firstInteraction = stretchingInteraction
  6 1 3 2
  ≤-refl
  (Data.Nat.Base.s≤s Data.Nat.Base.z≤n)

secondInteraction : FiniteStretchingInteraction 2
secondInteraction = stretchingInteraction
  8 2 2 2
  ≤-refl
  ≤-refl

canonicalInteractionFamily : List (FiniteStretchingInteraction 2)
canonicalInteractionFamily = firstInteraction ∷ secondInteraction ∷ []

canonicalRawStretchingTotal :
  sumRawStretching canonicalInteractionFamily ≡ 14
canonicalRawStretchingTotal = refl

canonicalControlledTotal :
  sumControlledStretching canonicalInteractionFamily ≡ 20
canonicalControlledTotal = refl

canonicalFiniteDepletionBound :
  sumRawStretching canonicalInteractionFamily
  ≤ sumControlledStretching canonicalInteractionFamily
canonicalFiniteDepletionBound =
  finiteSumGeometricDepletion canonicalInteractionFamily

------------------------------------------------------------------------
-- Cross-pollination with the existing exact stretching receipt.
------------------------------------------------------------------------

existingStretchingReceipt : Existing.NSVorticityStretchingExactReceipt
existingStretchingReceipt = Existing.canonicalNSVorticityStretchingExactReceipt

existingClayPromotionRemainsFalse :
  Existing.noClayPromotion existingStretchingReceipt ≡ false
existingClayPromotionRemainsFalse = Existing.clayPromotionStaysFalse

record ContinuumGeometricDepletionBoundary : Set₁ where
  field
    VorticityField : Set
    StrainField : Set
    biotSavartKernelRepresentation : Set
    directionFieldAwayFromZeros : Set
    holderDirectionCoherence : Set
    singularKernelIntegrability : Set
    continuumStretchingIntegralBound : Set
    depletedBKMIntegral : Set
    continuationTheorem : Set
    globalRegularityConclusion : Set

record FiniteVorticityDepletionCertificate : Set where
  field
    pointwise : ∀ {coherenceBound}
      (interaction : FiniteStretchingInteraction coherenceBound) →
      rawStretching interaction ≤ controlledContribution interaction
    finiteSum : ∀ {coherenceBound}
      (interactions : List (FiniteStretchingInteraction coherenceBound)) →
      sumRawStretching interactions ≤ sumControlledStretching interactions
    canonicalExample :
      sumRawStretching canonicalInteractionFamily
      ≤ sumControlledStretching canonicalInteractionFamily
    clayStillFalse : Existing.noClayPromotion existingStretchingReceipt ≡ false

canonicalFiniteVorticityDepletionCertificate :
  FiniteVorticityDepletionCertificate
canonicalFiniteVorticityDepletionCertificate = record
  { pointwise = pointwiseGeometricDepletion
  ; finiteSum = finiteSumGeometricDepletion
  ; canonicalExample = canonicalFiniteDepletionBound
  ; clayStillFalse = existingClayPromotionRemainsFalse
  }
