module DASHI.Foundations.DivergenceComparisonPackage where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Divergences are typed together with their domain and transfer laws.  The
-- package deliberately avoids a global winner: optimization, fail-closed
-- certification, and information accounting receive different defaults.

record OrderedDivergenceScalar : Set₁ where
  field
    Scalar : Set
    zero one : Scalar
    add mul : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

open OrderedDivergenceScalar public

two : (S : OrderedDivergenceScalar) → Scalar S
two S = add S (one S) (one S)

data DivergenceKind : Set where
  totalVariation : DivergenceKind
  squaredHellinger : DivergenceKind
  kullbackLeibler : DivergenceKind
  jensenShannon : DivergenceKind

data DivergenceRole : Set where
  optimizationLoss : DivergenceRole
  failClosedCertificate : DivergenceRole
  informationAccounting : DivergenceRole

defaultDivergenceForRole : DivergenceRole → DivergenceKind
defaultDivergenceForRole optimizationLoss = squaredHellinger
defaultDivergenceForRole failClosedCertificate = totalVariation
defaultDivergenceForRole informationAccounting = jensenShannon

record DivergenceComparisonPackage
  (Distribution : Set)
  (S : OrderedDivergenceScalar) : Set₁ where
  field
    TV HellingerSq KL JS :
      Distribution → Distribution → Scalar S

    AbsolutelyContinuous :
      Distribution → Distribution → Set

    DefinedKL :
      Distribution → Distribution → Set

    JSFinite :
      Distribution → Distribution → Set

    klDomainImpliesAbsoluteContinuity :
      ∀ P Q →
      DefinedKL P Q →
      AbsolutelyContinuous P Q

    hellingerSquaredBelowTV :
      ∀ P Q →
      LessEqual S (HellingerSq P Q) (TV P Q)

    tvSquaredBelowTwoHellingerSquared :
      ∀ P Q →
      LessEqual S
        (mul S (TV P Q) (TV P Q))
        (mul S (two S) (HellingerSq P Q))

    pinskerSquared :
      ∀ P Q →
      DefinedKL P Q →
      LessEqual S
        (mul S (two S) (mul S (TV P Q) (TV P Q)))
        (KL P Q)

    jsFiniteWithoutSharedSupport :
      ∀ P Q →
      JSFinite P Q

    jsSymmetric :
      ∀ P Q →
      JS P Q ≡ JS Q P

open DivergenceComparisonPackage public

record DivergenceEstimatorCertificate
  {Distribution : Set}
  {S : OrderedDivergenceScalar}
  (P : DivergenceComparisonPackage Distribution S)
  (kind : DivergenceKind) : Set₁ where
  field
    Estimate : Set
    estimate : Distribution → Distribution → Estimate
    varianceBound : Estimate → Scalar S
    supportAssumptions : Distribution → Distribution → Set
    estimatorCertified : Bool
    estimatorCertifiedIsTrue : estimatorCertified ≡ true

open DivergenceEstimatorCertificate public

record DashiDivergencePolicy : Set where
  field
    optimizationPrimary : DivergenceKind
    externalRobustnessCertificate : DivergenceKind
    densityRatioInformationMetric : DivergenceKind
    supportMismatchFallback : DivergenceKind

    optimizationPrimaryIsSquaredHellinger :
      optimizationPrimary ≡ squaredHellinger
    robustnessIsTV :
      externalRobustnessCertificate ≡ totalVariation
    densityRatioMetricIsKL :
      densityRatioInformationMetric ≡ kullbackLeibler
    supportMismatchFallbackIsJS :
      supportMismatchFallback ≡ jensenShannon

open DashiDivergencePolicy public

canonicalDashiDivergencePolicy : DashiDivergencePolicy
canonicalDashiDivergencePolicy =
  record
    { optimizationPrimary = squaredHellinger
    ; externalRobustnessCertificate = totalVariation
    ; densityRatioInformationMetric = kullbackLeibler
    ; supportMismatchFallback = jensenShannon
    ; optimizationPrimaryIsSquaredHellinger = refl
    ; robustnessIsTV = refl
    ; densityRatioMetricIsKL = refl
    ; supportMismatchFallbackIsJS = refl
    }

record NoUniversalDivergenceDominanceBoundary : Set where
  field
    universalStrictWinnerPromoted : Bool
    universalStrictWinnerPromotedIsFalse :
      universalStrictWinnerPromoted ≡ false

noUniversalDivergenceDominanceBoundary :
  NoUniversalDivergenceDominanceBoundary
noUniversalDivergenceDominanceBoundary =
  record
    { universalStrictWinnerPromoted = false
    ; universalStrictWinnerPromotedIsFalse = refl
    }
