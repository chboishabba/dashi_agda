module DASHI.Physics.Closure.NSTriadKNPhysicalGramOperatorAssembly where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Set; Setω)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNExactAlgebraicRetainedTriadFiber as Exact

------------------------------------------------------------------------
-- Finite-shell Gram assembly.
--
-- This is deliberately a scalar/vector construction, separate from the
-- diagnostic Nat count kernel.  It stops before inverse-square-root
-- normalization: an incidence Gram form can have a nontrivial kernel.
------------------------------------------------------------------------

record FiniteShellInnerProductSpace
    (S : Exact.ExactScalarOperations) : Set₁ where
  constructor mkFiniteShellInnerProductSpace
  field
    Vector : Set
    zeroVector : Vector
    _+ᵥ_ : Vector → Vector → Vector
    _•_ : Exact.ExactScalarOperations.Carrier S → Vector → Vector
    inner : Vector → Vector → Exact.ExactScalarOperations.Carrier S

    innerZeroRight :
      (x : Vector) →
      inner x zeroVector ≡ Exact.ExactScalarOperations.zero S

    innerAddRight :
      (x y z : Vector) →
      inner x (y +ᵥ z) ≡
      Exact.ExactScalarOperations._+_ S (inner x y) (inner x z)

    -- The rank-one identity is the finite-dimensional inner-product law
    -- needed below.  A concrete real/Hilbert implementation must prove it;
    -- it is not a retained-triad or Schur assumption.
    rankOneQuadraticFormula :
      (coefficient : Exact.ExactScalarOperations.Carrier S) →
      (b x : Vector) →
      inner x
        ((Exact.ExactScalarOperations._*_ S coefficient (inner b x)) • b) ≡
      Exact.ExactScalarOperations._*_ S coefficient
        (Exact.ExactScalarOperations._*_ S (inner b x) (inner b x))

    rankOneSum :
      {A : Set} →
      (A → Exact.ExactScalarOperations.Carrier S) →
      (A → Vector) → List A → Vector → Vector

    rankOneSumQuadraticFormula :
      {A : Set} →
      (coefficient : A → Exact.ExactScalarOperations.Carrier S) →
      (b : A → Vector) →
      (xs : List A) → (x : Vector) →
      inner x (rankOneSum coefficient b xs x) ≡
      Exact.weightedListSum {S = S}
        (λ a → Exact.ExactScalarOperations._*_ S (coefficient a)
          (Exact.ExactScalarOperations._*_ S (inner (b a) x) (inner (b a) x))) xs

    rankOneSumSelfAdjoint :
      {A : Set} →
      (coefficient : A → Exact.ExactScalarOperations.Carrier S) →
      (b : A → Vector) → (xs : List A) → (x y : Vector) →
      inner x (rankOneSum coefficient b xs y) ≡
      inner (rankOneSum coefficient b xs x) y

open FiniteShellInnerProductSpace public

vectorListSum :
  {S : Exact.ExactScalarOperations} →
  (H : FiniteShellInnerProductSpace S) →
  List (Vector H) → Vector H
vectorListSum H [] = zeroVector H
vectorListSum H (x ∷ xs) = _+ᵥ_ H x (vectorListSum H xs)

rankOneApply :
  {S : Exact.ExactScalarOperations} →
  (H : FiniteShellInnerProductSpace S) →
  Exact.ExactScalarOperations.Carrier S → Vector H → Vector H → Vector H
rankOneApply {S = S} H coefficient b x =
  _•_ H
    (Exact.ExactScalarOperations._*_ S coefficient (inner H b x))
    b

------------------------------------------------------------------------
-- The physical shell datum fixes the retained triads, their incidence
-- vectors, and the exact Python coefficients.  The two coefficient facts
-- are the only physical sign/order input used to derive the Gram order.
------------------------------------------------------------------------

record PhysicalGramAssemblyData
    {S : Exact.ExactScalarOperations}
    (surface : Exact.FiniteTriadModeSurface S)
    (profile : Exact.AdmissibleAmplitudeProfile surface)
    (H : FiniteShellInnerProductSpace S) : Setω where
  constructor mkPhysicalGramAssemblyData
  field
    retainedTriads : List (Exact.TriadOf surface)
    incidenceVector : Exact.TriadOf surface → Vector H

    negativeCoefficient :
      Exact.TriadOf surface → Exact.ExactScalarOperations.Carrier S
    absoluteCoefficient :
      Exact.TriadOf surface → Exact.ExactScalarOperations.Carrier S

    negativeCoefficientFormula :
      (τ : Exact.TriadOf surface) →
      negativeCoefficient τ ≡ Exact.triadNegativeWeight profile τ
    absoluteCoefficientFormula :
      (τ : Exact.TriadOf surface) →
      absoluteCoefficient τ ≡ Exact.triadAbsoluteWeight profile τ

    -- Ordered scalar consequences required of the chosen exact scalar model.
    Nonnegative : Exact.ExactScalarOperations.Carrier S → Set
    _≼_ : Exact.ExactScalarOperations.Carrier S →
          Exact.ExactScalarOperations.Carrier S → Set

    negativeRankOneNonnegative :
      (τ : Exact.TriadOf surface) → (x : Vector H) →
      Nonnegative
        (Exact.ExactScalarOperations._*_ S (negativeCoefficient τ)
          (Exact.ExactScalarOperations._*_ S
            (inner H (incidenceVector τ) x)
            (inner H (incidenceVector τ) x)))

    absoluteRankOneNonnegative :
      (τ : Exact.TriadOf surface) → (x : Vector H) →
      Nonnegative
        (Exact.ExactScalarOperations._*_ S (absoluteCoefficient τ)
          (Exact.ExactScalarOperations._*_ S
            (inner H (incidenceVector τ) x)
            (inner H (incidenceVector τ) x)))

    negativeRankOneDominatedByAbsolute :
      (τ : Exact.TriadOf surface) → (x : Vector H) →
      Exact.ExactScalarOperations._*_ S (negativeCoefficient τ)
        (Exact.ExactScalarOperations._*_ S
          (inner H (incidenceVector τ) x)
          (inner H (incidenceVector τ) x))
      ≼
      Exact.ExactScalarOperations._*_ S (absoluteCoefficient τ)
        (Exact.ExactScalarOperations._*_ S
          (inner H (incidenceVector τ) x)
          (inner H (incidenceVector τ) x))

    sumNonnegative :
      (weight : Exact.TriadOf surface → Exact.ExactScalarOperations.Carrier S) →
      (xs : List (Exact.TriadOf surface)) →
      ((τ : Exact.TriadOf surface) → Exact._∈_ τ xs → Nonnegative (weight τ)) →
      Nonnegative (Exact.weightedListSum {S = S} weight xs)

    sumDominated :
      (left right : Exact.TriadOf surface → Exact.ExactScalarOperations.Carrier S) →
      (xs : List (Exact.TriadOf surface)) →
      ((τ : Exact.TriadOf surface) → Exact._∈_ τ xs → left τ ≼ right τ) →
      Exact.weightedListSum {S = S} left xs ≼
      Exact.weightedListSum {S = S} right xs

open PhysicalGramAssemblyData public

squareInner :
  {S : Exact.ExactScalarOperations} →
  (H : FiniteShellInnerProductSpace S) →
  Vector H → Vector H →
  Exact.ExactScalarOperations.Carrier S
squareInner {S = S} H b x =
  Exact.ExactScalarOperations._*_ S (inner H b x) (inner H b x)

absoluteRankOneTerm :
  {S : Exact.ExactScalarOperations} →
  {surface : Exact.FiniteTriadModeSurface S} →
  {profile : Exact.AdmissibleAmplitudeProfile surface} →
  {H : FiniteShellInnerProductSpace S} →
  PhysicalGramAssemblyData surface profile H →
  Exact.TriadOf surface → Vector H → Vector H
absoluteRankOneTerm {H = H} Hdata τ x =
  rankOneApply H
    (absoluteCoefficient Hdata τ)
    (incidenceVector Hdata τ) x

negativeRankOneTerm :
  {S : Exact.ExactScalarOperations} →
  {surface : Exact.FiniteTriadModeSurface S} →
  {profile : Exact.AdmissibleAmplitudeProfile surface} →
  {H : FiniteShellInnerProductSpace S} →
  PhysicalGramAssemblyData surface profile H →
  Exact.TriadOf surface → Vector H → Vector H
negativeRankOneTerm {H = H} Hdata τ x =
  rankOneApply H
    (negativeCoefficient Hdata τ)
    (incidenceVector Hdata τ) x

absoluteTerms :
  {S : Exact.ExactScalarOperations} →
  {surface : Exact.FiniteTriadModeSurface S} →
  {profile : Exact.AdmissibleAmplitudeProfile surface} →
  {H : FiniteShellInnerProductSpace S} →
  PhysicalGramAssemblyData surface profile H → Vector H →
  List (Exact.TriadOf surface) → List (Vector H)
absoluteTerms Hdata x [] = []
absoluteTerms Hdata x (τ ∷ τs) =
  absoluteRankOneTerm Hdata τ x ∷ absoluteTerms Hdata x τs

negativeTerms :
  {S : Exact.ExactScalarOperations} →
  {surface : Exact.FiniteTriadModeSurface S} →
  {profile : Exact.AdmissibleAmplitudeProfile surface} →
  {H : FiniteShellInnerProductSpace S} →
  PhysicalGramAssemblyData surface profile H → Vector H →
  List (Exact.TriadOf surface) → List (Vector H)
negativeTerms Hdata x [] = []
negativeTerms Hdata x (τ ∷ τs) =
  negativeRankOneTerm Hdata τ x ∷ negativeTerms Hdata x τs

physicalLAbs :
  {S : Exact.ExactScalarOperations} →
  {surface : Exact.FiniteTriadModeSurface S} →
  {profile : Exact.AdmissibleAmplitudeProfile surface} →
  {H : FiniteShellInnerProductSpace S} →
  (Hdata : PhysicalGramAssemblyData surface profile H) → Vector H → Vector H
physicalLAbs {H = H} Hdata x =
  rankOneSum H
    (absoluteCoefficient Hdata)
    (incidenceVector Hdata)
    (retainedTriads Hdata) x

physicalLNeg :
  {S : Exact.ExactScalarOperations} →
  {surface : Exact.FiniteTriadModeSurface S} →
  {profile : Exact.AdmissibleAmplitudeProfile surface} →
  {H : FiniteShellInnerProductSpace S} →
  (Hdata : PhysicalGramAssemblyData surface profile H) → Vector H → Vector H
physicalLNeg {H = H} Hdata x =
  rankOneSum H
    (negativeCoefficient Hdata)
    (incidenceVector Hdata)
    (retainedTriads Hdata) x

------------------------------------------------------------------------
-- Finite-fold expansion.  The induction is purely linear algebra; it does
-- not use any profile budget or a count-kernel surrogate.
------------------------------------------------------------------------

lAbsQuadraticExpansion :
  {S : Exact.ExactScalarOperations} →
  {surface : Exact.FiniteTriadModeSurface S} →
  {profile : Exact.AdmissibleAmplitudeProfile surface} →
  {H : FiniteShellInnerProductSpace S} →
  (Hdata : PhysicalGramAssemblyData surface profile H) → (x : Vector H) →
  inner H x (physicalLAbs Hdata x) ≡
  Exact.weightedListSum {S = S}
    (λ τ → Exact.ExactScalarOperations._*_ S (absoluteCoefficient Hdata τ)
      (Exact.ExactScalarOperations._*_ S
        (inner H (incidenceVector Hdata τ) x)
        (inner H (incidenceVector Hdata τ) x)))
    (retainedTriads Hdata)
lAbsQuadraticExpansion {H = H} Hdata x =
  rankOneSumQuadraticFormula H
    (absoluteCoefficient Hdata)
    (incidenceVector Hdata)
    (retainedTriads Hdata) x

-- The negative expansion has the same finite-fold proof.  It is kept as a
-- named theorem because it is the exact entry point for the operator order.
lNegQuadraticExpansion :
  {S : Exact.ExactScalarOperations} →
  {surface : Exact.FiniteTriadModeSurface S} →
  {profile : Exact.AdmissibleAmplitudeProfile surface} →
  {H : FiniteShellInnerProductSpace S} →
  (Hdata : PhysicalGramAssemblyData surface profile H) → (x : Vector H) →
  inner H x (physicalLNeg Hdata x) ≡
  Exact.weightedListSum {S = S}
    (λ τ → Exact.ExactScalarOperations._*_ S (negativeCoefficient Hdata τ)
      (Exact.ExactScalarOperations._*_ S
        (inner H (incidenceVector Hdata τ) x)
        (inner H (incidenceVector Hdata τ) x)))
    (retainedTriads Hdata)
lNegQuadraticExpansion {H = H} Hdata x =
  rankOneSumQuadraticFormula H
    (negativeCoefficient Hdata)
    (incidenceVector Hdata)
    (retainedTriads Hdata) x

lAbsSelfAdjoint :
  {S : Exact.ExactScalarOperations} →
  {surface : Exact.FiniteTriadModeSurface S} →
  {profile : Exact.AdmissibleAmplitudeProfile surface} →
  {H : FiniteShellInnerProductSpace S} →
  (Hdata : PhysicalGramAssemblyData surface profile H) →
  (x y : Vector H) →
  inner H x (physicalLAbs Hdata y) ≡ inner H (physicalLAbs Hdata x) y
lAbsSelfAdjoint {H = H} Hdata x y =
  rankOneSumSelfAdjoint H
    (absoluteCoefficient Hdata) (incidenceVector Hdata)
    (retainedTriads Hdata) x y

lNegSelfAdjoint :
  {S : Exact.ExactScalarOperations} →
  {surface : Exact.FiniteTriadModeSurface S} →
  {profile : Exact.AdmissibleAmplitudeProfile surface} →
  {H : FiniteShellInnerProductSpace S} →
  (Hdata : PhysicalGramAssemblyData surface profile H) →
  (x y : Vector H) →
  inner H x (physicalLNeg Hdata y) ≡ inner H (physicalLNeg Hdata x) y
lNegSelfAdjoint {H = H} Hdata x y =
  rankOneSumSelfAdjoint H
    (negativeCoefficient Hdata) (incidenceVector Hdata)
    (retainedTriads Hdata) x y

------------------------------------------------------------------------
-- The first analytic operator consequence: finite summation transfers the
-- termwise physical inequality m^- ≤ m^abs to quadratic-form order.
------------------------------------------------------------------------

lNegPositive :
  {S : Exact.ExactScalarOperations} →
  {surface : Exact.FiniteTriadModeSurface S} →
  {profile : Exact.AdmissibleAmplitudeProfile surface} →
  {H : FiniteShellInnerProductSpace S} →
  (Hdata : PhysicalGramAssemblyData surface profile H) → (x : Vector H) →
  PhysicalGramAssemblyData.Nonnegative Hdata
    (inner H x (physicalLNeg Hdata x))
lNegPositive {S = S} {H = H} Hdata x rewrite lNegQuadraticExpansion Hdata x =
  sumNonnegative Hdata
    (λ τ → Exact.ExactScalarOperations._*_ S (negativeCoefficient Hdata τ)
      (Exact.ExactScalarOperations._*_ S
        (inner H (incidenceVector Hdata τ) x)
        (inner H (incidenceVector Hdata τ) x)))
    (retainedTriads Hdata)
    (λ τ _ → negativeRankOneNonnegative Hdata τ x)

lAbsPositive :
  {S : Exact.ExactScalarOperations} →
  {surface : Exact.FiniteTriadModeSurface S} →
  {profile : Exact.AdmissibleAmplitudeProfile surface} →
  {H : FiniteShellInnerProductSpace S} →
  (Hdata : PhysicalGramAssemblyData surface profile H) → (x : Vector H) →
  PhysicalGramAssemblyData.Nonnegative Hdata
    (inner H x (physicalLAbs Hdata x))
lAbsPositive {S = S} {H = H} Hdata x rewrite lAbsQuadraticExpansion Hdata x =
  sumNonnegative Hdata
    (λ τ → Exact.ExactScalarOperations._*_ S (absoluteCoefficient Hdata τ)
      (Exact.ExactScalarOperations._*_ S
        (inner H (incidenceVector Hdata τ) x)
        (inner H (incidenceVector Hdata τ) x)))
    (retainedTriads Hdata)
    (λ τ _ → absoluteRankOneNonnegative Hdata τ x)

lNegDominatedByLAbs :
  {S : Exact.ExactScalarOperations} →
  {surface : Exact.FiniteTriadModeSurface S} →
  {profile : Exact.AdmissibleAmplitudeProfile surface} →
  {H : FiniteShellInnerProductSpace S} →
  (Hdata : PhysicalGramAssemblyData surface profile H) → (x : Vector H) →
  PhysicalGramAssemblyData._≼_ Hdata
    (inner H x (physicalLNeg Hdata x))
    (inner H x (physicalLAbs Hdata x))
lNegDominatedByLAbs {S = S} {H = H} Hdata x
  rewrite lNegQuadraticExpansion Hdata x
        | lAbsQuadraticExpansion Hdata x =
  sumDominated Hdata
    (λ τ → Exact.ExactScalarOperations._*_ S (negativeCoefficient Hdata τ)
      (Exact.ExactScalarOperations._*_ S
        (inner H (incidenceVector Hdata τ) x)
        (inner H (incidenceVector Hdata τ) x)))
    (λ τ → Exact.ExactScalarOperations._*_ S (absoluteCoefficient Hdata τ)
      (Exact.ExactScalarOperations._*_ S
        (inner H (incidenceVector Hdata τ) x)
        (inner H (incidenceVector Hdata τ) x)))
    (retainedTriads Hdata)
    (λ τ _ → negativeRankOneDominatedByAbsolute Hdata τ x)

------------------------------------------------------------------------
-- Normalization is intentionally only an exposed boundary.  The ambient
-- Gram form may be singular, so neither an inverse nor im(L)=ker(L)^⊥ is
-- assumed here.
------------------------------------------------------------------------

PositiveGramCarrier :
  {S : Exact.ExactScalarOperations} →
  {surface : Exact.FiniteTriadModeSurface S} →
  {profile : Exact.AdmissibleAmplitudeProfile surface} →
  {H : FiniteShellInnerProductSpace S} →
  (Hdata : PhysicalGramAssemblyData surface profile H) → Vector H → Set
PositiveGramCarrier {S = S} {H = H} Hdata x =
  (y : Vector H) →
  physicalLAbs Hdata y ≡ zeroVector H →
  inner H x y ≡
  Exact.ExactScalarOperations.zero S

physicalGramNormalizationClosed : Bool
physicalGramNormalizationClosed = false

physicalGramNormalizationClosedIsFalse :
  physicalGramNormalizationClosed ≡ false
physicalGramNormalizationClosedIsFalse = refl
