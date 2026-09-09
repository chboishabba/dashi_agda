module DASHI.Physics.YangMills.BalabanMarkedHessianReferenceAnchorExact where

------------------------------------------------------------------------
-- ROW-C MARKED HESSIAN: COMPARISON + REFERENCE ANCHOR
--
-- The canonical CMP99/CMP116 theorem controls a DOMAIN DIFFERENCE
--
--   |H_Ω - H_Ω'| <= M(Ω,Ω').
--
-- It does not by itself control |H_Ω|.  The least-privilege absolute compiler
-- therefore adds exactly one independent reference-domain anchor
--
--   |H_Ω'| <= A(Ω')
--
-- and standard additive recomposition
--
--   H_Ω = (H_Ω - H_Ω') + H_Ω'.
--
-- The resulting absolute estimate is derived, not stored:
--
--   |H_Ω| <= M(Ω,Ω') + A(Ω').
--
-- A vanishing reference is a specialization with A = 0, never an implicit
-- property of the comparison theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; 0ℝ ; _+ℝ_ ; _-ℝ_ ; absℝ ; _≤ℝ_
  ; ≤ℝ-refl ; ≤ℝ-trans ; +-mono-≤ ; absZero ; absAddSubadditive
  ; +-identityʳ )

import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Marked

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

------------------------------------------------------------------------
-- Exact reference-domain anchor on the same localized Hessian carrier.
------------------------------------------------------------------------

record MarkedHessianReferenceAnchor
    {Domain Background History : Set}
    (walkData : Marked.MarkedWalkHessianData Domain Background History)
    (scale : ℕ)
    (Ω Ω′ : Domain)
    (U : Background)
    (history : History)
    (X : Marked.Localisation walkData)
    (x y : Marked.Cube walkData) : Set where
  constructor marked-hessian-reference-anchor
  field
    referenceMajorant : ℝ

    -- Standard real-algebra recomposition.  This is kept explicit because the
    -- shared RealAnalysisAxioms surface intentionally does not expose a global
    -- subtraction-as-addition theorem.
    recomposition :
      Marked.localisedHessian walkData scale Ω U history X x y
      ≡
      (Marked.localisedHessian walkData scale Ω U history X x y
        -ℝ Marked.localisedHessian walkData scale Ω′ U history X x y)
      +ℝ
      Marked.localisedHessian walkData scale Ω′ U history X x y

    referenceAbsoluteBound :
      absℝ (Marked.localisedHessian walkData scale Ω′ U history X x y)
      ≤ℝ referenceMajorant

open MarkedHessianReferenceAnchor public

anchoredMarkedHessianBound :
  ∀ {Domain Background History}
  (walkData : Marked.MarkedWalkHessianData Domain Background History)
  (scale : ℕ)
  (Ω Ω′ : Domain)
  (U : Background)
  (history : History)
  (X : Marked.Localisation walkData)
  (x y : Marked.Cube walkData)
  (anchor : MarkedHessianReferenceAnchor
    walkData scale Ω Ω′ U history X x y) →
  absℝ (Marked.localisedHessian walkData scale Ω U history X x y)
  ≤ℝ
  Marked.hessianMarkedMajorant walkData scale Ω Ω′ U history X x y
  +ℝ referenceMajorant anchor
anchoredMarkedHessianBound walkData scale Ω Ω′ U history X x y anchor
  rewrite recomposition anchor =
  ≤ℝ-trans
    (absAddSubadditive
      (Marked.localisedHessian walkData scale Ω U history X x y
        -ℝ Marked.localisedHessian walkData scale Ω′ U history X x y)
      (Marked.localisedHessian walkData scale Ω′ U history X x y))
    (+-mono-≤
      (Marked.markedLocalisedHessianEstimate
        walkData scale Ω Ω′ U history X x y)
      (referenceAbsoluteBound anchor))

------------------------------------------------------------------------
-- Vanishing-reference specialization.
------------------------------------------------------------------------

record VanishingMarkedHessianReference
    {Domain Background History : Set}
    (walkData : Marked.MarkedWalkHessianData Domain Background History)
    (scale : ℕ)
    (Ω Ω′ : Domain)
    (U : Background)
    (history : History)
    (X : Marked.Localisation walkData)
    (x y : Marked.Cube walkData) : Set where
  constructor vanishing-marked-hessian-reference
  field
    recomposition :
      Marked.localisedHessian walkData scale Ω U history X x y
      ≡
      (Marked.localisedHessian walkData scale Ω U history X x y
        -ℝ Marked.localisedHessian walkData scale Ω′ U history X x y)
      +ℝ
      Marked.localisedHessian walkData scale Ω′ U history X x y

    referenceVanishes :
      Marked.localisedHessian walkData scale Ω′ U history X x y ≡ 0ℝ

open VanishingMarkedHessianReference public

vanishingReferenceAsAnchor :
  ∀ {Domain Background History}
  {walkData : Marked.MarkedWalkHessianData Domain Background History}
  {scale : ℕ} {Ω Ω′ : Domain} {U : Background} {history : History}
  {X : Marked.Localisation walkData} {x y : Marked.Cube walkData} →
  VanishingMarkedHessianReference walkData scale Ω Ω′ U history X x y →
  MarkedHessianReferenceAnchor walkData scale Ω Ω′ U history X x y
vanishingReferenceAsAnchor vanishing =
  marked-hessian-reference-anchor
    0ℝ
    (VanishingMarkedHessianReference.recomposition vanishing)
    referenceBound
  where
    referenceBound :
      absℝ
        (Marked.localisedHessian _ _ _ _ _ _ _ _ _)
      ≤ℝ 0ℝ
    referenceBound
      rewrite VanishingMarkedHessianReference.referenceVanishes vanishing
      | absZero = ≤ℝ-refl

vanishingReferenceMarkedHessianBound :
  ∀ {Domain Background History}
  (walkData : Marked.MarkedWalkHessianData Domain Background History)
  (scale : ℕ)
  (Ω Ω′ : Domain)
  (U : Background)
  (history : History)
  (X : Marked.Localisation walkData)
  (x y : Marked.Cube walkData)
  (vanishing : VanishingMarkedHessianReference
    walkData scale Ω Ω′ U history X x y) →
  absℝ (Marked.localisedHessian walkData scale Ω U history X x y)
  ≤ℝ
  Marked.hessianMarkedMajorant walkData scale Ω Ω′ U history X x y
vanishingReferenceMarkedHessianBound walkData scale Ω Ω′ U history X x y vanishing
  rewrite sym
    (+-identityʳ
      (Marked.hessianMarkedMajorant walkData scale Ω Ω′ U history X x y)) =
  anchoredMarkedHessianBound
    walkData scale Ω Ω′ U history X x y
    (vanishingReferenceAsAnchor vanishing)

------------------------------------------------------------------------
-- Firewalls / introspective boundary.
------------------------------------------------------------------------

data ComparisonMeansAbsoluteBoundPermission : Set where

data ComparisonMeansReferenceVanishesPermission : Set where

data ReferenceBoundMeansZeroReferencePermission : Set where

data AbsoluteMarkedBoundMeansCMP116PhysicalIdentificationPermission : Set where

comparisonDoesNotManufactureAbsoluteBound :
  ComparisonMeansAbsoluteBoundPermission → ⊥
comparisonDoesNotManufactureAbsoluteBound ()

comparisonDoesNotManufactureVanishingReference :
  ComparisonMeansReferenceVanishesPermission → ⊥
comparisonDoesNotManufactureVanishingReference ()

boundedReferenceDoesNotMeanVanishingReference :
  ReferenceBoundMeansZeroReferencePermission → ⊥
boundedReferenceDoesNotMeanVanishingReference ()

absoluteMarkedBoundDoesNotIdentifyPhysicalCMP116Hessian :
  AbsoluteMarkedBoundMeansCMP116PhysicalIdentificationPermission → ⊥
absoluteMarkedBoundDoesNotIdentifyPhysicalCMP116Hessian ()

record AnchoredMarkedHessianBoundary : Set where
  constructor anchored-marked-hessian-boundary
  field
    comparisonTheoremReused : Bool
    referenceAnchorExplicit : Bool
    recompositionExplicit : Bool
    absoluteBoundDerivedByTriangle : Bool
    vanishingReferenceOptionalSpecialCase : Bool
    comparisonAutomaticallyAbsolute : Bool
    referenceAutomaticallyZero : Bool
    physicalCMP116IdentificationManufactured : Bool

canonicalAnchoredMarkedHessianBoundary : AnchoredMarkedHessianBoundary
canonicalAnchoredMarkedHessianBoundary =
  anchored-marked-hessian-boundary
    true true true true true false false false
