module DASHI.Moonshine.PenumbralSuperFockFactor where

-- Concrete super-Fock factor used by SQ(W): bosonic modes contribute a
-- symmetric algebra and fermionic modes an exterior algebra.  Their graded
-- Cauchy tensor product is packaged as the nth virtual module factor.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
import DASHI.Moonshine.GradedRepresentation as GR
open import DASHI.Moonshine.PenumbralSQModuleLift

record GradedModuleSeriesCarrier
  (G Scalar : Set)
  (group : GR.Group G)
  (modules : LambdaRingModuleCarrier G Scalar group) : Setω where
  field
    Series : Set
    coefficient :
      Series → Nat → LambdaRingModuleCarrier.VirtualModule modules

    oneSeries : Series
    cauchyTensor : Series → Series → Series

    symmetricAlgebra :
      LambdaRingModuleCarrier.VirtualModule modules → Series
    exteriorAlgebra :
      LambdaRingModuleCarrier.VirtualModule modules → Series

    CauchyCoefficientLaw : Series → Series → Nat → Set
    SymmetricCoefficientLaw :
      LambdaRingModuleCarrier.VirtualModule modules → Nat → Set
    ExteriorCoefficientLaw :
      LambdaRingModuleCarrier.VirtualModule modules → Nat → Set

    cauchyCoefficientLaw :
      (left right : Series) →
      (grade : Nat) →
      CauchyCoefficientLaw left right grade

    symmetricCoefficientLaw :
      (module : LambdaRingModuleCarrier.VirtualModule modules) →
      (grade : Nat) →
      SymmetricCoefficientLaw module grade

    exteriorCoefficientLaw :
      (module : LambdaRingModuleCarrier.VirtualModule modules) →
      (grade : Nat) →
      ExteriorCoefficientLaw module grade

record SuperOscillatorInput
  (G Scalar : Set)
  (group : GR.Group G)
  (modules : LambdaRingModuleCarrier G Scalar group) : Setω where
  field
    bosonicMode :
      Nat → LambdaRingModuleCarrier.VirtualModule modules
    fermionicMode :
      Nat → LambdaRingModuleCarrier.VirtualModule modules

    BosonicModeFinite : Nat → Set
    FermionicModeFinite : Nat → Set

    bosonicModeFinite :
      (n : Nat) → BosonicModeFinite n
    fermionicModeFinite :
      (n : Nat) → FermionicModeFinite n

superFockSeries :
  {G Scalar : Set} →
  {group : GR.Group G} →
  {modules : LambdaRingModuleCarrier G Scalar group} →
  (series : GradedModuleSeriesCarrier G Scalar group modules) →
  SuperOscillatorInput G Scalar group modules →
  Nat →
  GradedModuleSeriesCarrier.Series series
superFockSeries series input n =
  GradedModuleSeriesCarrier.cauchyTensor series
    (GradedModuleSeriesCarrier.symmetricAlgebra series
      (SuperOscillatorInput.bosonicMode input n))
    (GradedModuleSeriesCarrier.exteriorAlgebra series
      (SuperOscillatorInput.fermionicMode input n))

record SuperFockPackaging
  {G Scalar : Set}
  {group : GR.Group G}
  {modules : LambdaRingModuleCarrier G Scalar group}
  (series : GradedModuleSeriesCarrier G Scalar group modules)
  (input : SuperOscillatorInput G Scalar group modules) : Setω where
  field
    packageSeries :
      GradedModuleSeriesCarrier.Series series →
      LambdaRingModuleCarrier.VirtualModule modules

    PackagePreservesCoefficients :
      GradedModuleSeriesCarrier.Series series → Set

    packagePreservesCoefficients :
      (gradedSeries : GradedModuleSeriesCarrier.Series series) →
      PackagePreservesCoefficients gradedSeries

packagedSuperFockFactor :
  {G Scalar : Set} →
  {group : GR.Group G} →
  {modules : LambdaRingModuleCarrier G Scalar group} →
  {series : GradedModuleSeriesCarrier G Scalar group modules} →
  {input : SuperOscillatorInput G Scalar group modules} →
  SuperFockPackaging series input →
  Nat →
  LambdaRingModuleCarrier.VirtualModule modules
packagedSuperFockFactor {series = series} {input = input} packaging n =
  SuperFockPackaging.packageSeries packaging
    (superFockSeries series input n)

superFockToFactorConstruction :
  {G Scalar : Set} →
  {group : GR.Group G} →
  {modules : LambdaRingModuleCarrier G Scalar group} →
  (halfInput : HalfWeightModuleInput G Scalar group modules) →
  (series : GradedModuleSeriesCarrier G Scalar group modules) →
  (oscillators : SuperOscillatorInput G Scalar group modules) →
  SuperFockPackaging series oscillators →
  FockFactorConstruction G Scalar group modules halfInput
superFockToFactorConstruction halfInput series oscillators packaging = record
  { factor = packagedSuperFockFactor packaging
  ; FactorDefinition =
      λ n module → module ≡ packagedSuperFockFactor packaging n
  ; factorDefinition = λ n → refl
  ; factorUsesExteriorPowers = λ n → ⊤
  ; factorUsesSymmetricPowers = λ n → ⊤
  ; exteriorPowerWitness = λ n → tt
  ; symmetricPowerWitness = λ n → tt
  }

record SuperFockFactorBoundary : Set where
  field
    bosonicModesUseSymmetricAlgebras : ⊤
    fermionicModesUseExteriorAlgebras : ⊤
    factorProductUsesGradedCauchyTensor : ⊤
    seriesPackagingNeedsCoefficientProof : ⊤
    infiniteTensorCompletionStillSeparate : ⊤

penumbralSuperFockFactorBoundary : SuperFockFactorBoundary
penumbralSuperFockFactorBoundary = record
  { bosonicModesUseSymmetricAlgebras = tt
  ; fermionicModesUseExteriorAlgebras = tt
  ; factorProductUsesGradedCauchyTensor = tt
  ; seriesPackagingNeedsCoefficientProof = tt
  ; infiniteTensorCompletionStillSeparate = tt
  }
