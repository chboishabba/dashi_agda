module DASHI.Moonshine.PenumbralMoonshineModule where

-- The representation-theoretic realization of a penumbral form.  Grades are
-- indexed by the residue/discriminant support rather than by Nat alone, and
-- virtuality is explicit because some distinguished coefficients are signed.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Unit using (⊤; tt)
import DASHI.Moonshine.GradedRepresentation as GR
open import DASHI.Moonshine.PenumbralLambency
open import DASHI.Moonshine.PenumbralVectorValuedForm

record VirtualRepresentationCarrier
  (G Scalar : Set)
  (group : GR.Group G) : Set₁ where
  field
    VirtualRepresentation : Set
    zeroVirtual : VirtualRepresentation
    addVirtual : VirtualRepresentation → VirtualRepresentation → VirtualRepresentation
    negateVirtual : VirtualRepresentation → VirtualRepresentation
    trace : G → VirtualRepresentation → Scalar

record PenumbralMoonshineRealization
  (formCarrier : VectorValuedModularCarrier)
  (arithmetic : LambencyArithmetic)
  {Discriminant : Set}
  (lambda : PenumbralLambdency arithmetic Discriminant)
  (support : PenumbralSupport formCarrier arithmetic lambda)
  (identityForm : PenumbralForm formCarrier arithmetic lambda support)
  : Setω where
  open VectorValuedModularCarrier formCarrier
  field
    G : Set
    group : GR.Group G
    virtualCarrier : VirtualRepresentationCarrier G Scalar group

    grade :
      PenumbralSupport.DiscriminantIndex support →
      VirtualRepresentationCarrier.VirtualRepresentation virtualCarrier

    twinedForm : G → Vector

    twinedWeakHolomorphy :
      (g : G) → weaklyHolomorphic (twinedForm g)

    twinedWeilTransformation :
      (g : G) →
      transformsFor (twinedForm g)
        (PenumbralForm.weilRepresentation identityForm)

    identityRecoversDistinguishedForm :
      twinedForm (GR.Group.identity group)
      ≡ PenumbralForm.form identityForm

    coefficientTraceLaw :
      (g : G) →
      (index : PenumbralSupport.DiscriminantIndex support) →
      coefficient (twinedForm g)
        (PenumbralSupport.residue support index)
        (PenumbralSupport.exponent support index)
      ≡
      VirtualRepresentationCarrier.trace virtualCarrier g (grade index)

record ProvenPenumbralFamily : Set₁ where
  field
    Discriminant : Set
    IsMinusThree IsMinusFour : Discriminant → Set
    FamilyMember : Discriminant → Set

    onlyMinusThreeOrMinusFour :
      (D0 : Discriminant) →
      FamilyMember D0 →
      IsMinusThree D0 ⊎ IsMinusFour D0

record PenumbralModuleBoundary : Set where
  field
    virtualModuleIsNotNecessarilyHonestModule : ⊤
    traceLawRequiredAtEveryGrade : ⊤
    identitySeriesDoesNotDetermineAllTwining : ⊤
    explicitVOAConstructionNotProvided : ⊤
    noAllDiscriminantsClassificationClaim : ⊤

penumbralModuleBoundary : PenumbralModuleBoundary
penumbralModuleBoundary = record
  { virtualModuleIsNotNecessarilyHonestModule = tt
  ; traceLawRequiredAtEveryGrade = tt
  ; identitySeriesDoesNotDetermineAllTwining = tt
  ; explicitVOAConstructionNotProvided = tt
  ; noAllDiscriminantsClassificationClaim = tt
  }
