module DASHI.Physics.YangMills.BalabanPeriodicTorus4Fourier where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier

------------------------------------------------------------------------
-- Exact finite-abelian Fourier authority on the literal four-torus.
--
-- Character orthogonality, inversion and Parseval are standard finite Fourier
-- analysis.  The record below fixes their hypotheses and, crucially, requires
-- them for the literal definitions in this module rather than for an unrelated
-- abstract transform.  All bond-field consequences are then kernel proofs.
------------------------------------------------------------------------

record FourierScalarOperations (Scalar Bound : Set) : Set₁ where
  field
    zeroScalar oneScalar : Scalar
    addScalar multiplyScalar : Scalar → Scalar → Scalar
    negateScalar conjugateScalar : Scalar → Scalar
    normalizationScalar cardinalityScalar : Scalar

    zeroBound : Bound
    addBound : Bound → Bound → Bound
    scaleBound : Scalar → Bound → Bound

open FourierScalarOperations public

sumScalarList :
  ∀ {A Scalar Bound : Set} →
  FourierScalarOperations Scalar Bound →
  (A → Scalar) → List A → Scalar
sumScalarList operations term [] = zeroScalar operations
sumScalarList operations term (x ∷ xs) =
  addScalar operations (term x) (sumScalarList operations term xs)

sumBoundList :
  ∀ {A Scalar Bound : Set} →
  FourierScalarOperations Scalar Bound →
  (A → Bound) → List A → Bound
sumBoundList operations term [] = zeroBound operations
sumBoundList operations term (x ∷ xs) =
  addBound operations (term x) (sumBoundList operations term xs)

kronecker :
  ∀ {A Scalar : Set} →
  DecidableEquality A → Scalar → Scalar → A → A → Scalar
kronecker decide zeroValue oneValue x y with decide x y
... | yes equality = oneValue
... | no inequality = zeroValue

SiteField : Nat → Set → Set
SiteField L Scalar = periodicTorus4Definition L → Scalar

MomentumField : Nat → Set → Set
MomentumField L Scalar = dualPeriodicTorus4Definition L → Scalar

record PeriodicTorus4FourierAuthority
    (L : Nat) (Scalar Bound : Set) : Set₁ where
  field
    operations : FourierScalarOperations Scalar Bound

    momentumAdd :
      dualPeriodicTorus4Definition L →
      dualPeriodicTorus4Definition L →
      dualPeriodicTorus4Definition L
    momentumNegate :
      dualPeriodicTorus4Definition L →
      dualPeriodicTorus4Definition L

    momentumCharacter :
      dualPeriodicTorus4Definition L →
      periodicTorus4Definition L → Scalar

    sourceMomentumCharacterMultiplication : ∀ k l x →
      momentumCharacter (momentumAdd k l) x ≡
      multiplyScalar operations
        (momentumCharacter k x)
        (momentumCharacter l x)

    sourceMomentumCharacterConjugation : ∀ k x →
      conjugateScalar operations (momentumCharacter k x) ≡
      momentumCharacter (momentumNegate k) x

    scalarSiteNormSq : SiteField L Scalar → Bound
    scalarMomentumNormSq : MomentumField L Scalar → Bound

open PeriodicTorus4FourierAuthority public

sumSites :
  ∀ {L Scalar Bound} →
  PeriodicTorus4FourierAuthority L Scalar Bound →
  (periodicTorus4Definition L → Scalar) → Scalar
sumSites authority term =
  sumScalarList (operations authority) term
    (elements (periodicTorus4Finite _))

sumMomenta :
  ∀ {L Scalar Bound} →
  PeriodicTorus4FourierAuthority L Scalar Bound →
  (dualPeriodicTorus4Definition L → Scalar) → Scalar
sumMomenta authority term =
  sumScalarList (operations authority) term
    (elements (momentumCharactersEnumerated _))

momentumCharacterDefinition :
  ∀ {L Scalar Bound} →
  PeriodicTorus4FourierAuthority L Scalar Bound →
  dualPeriodicTorus4Definition L →
  periodicTorus4Definition L → Scalar
momentumCharacterDefinition = momentumCharacter

momentumCharacterMultiplication :
  ∀ {L Scalar Bound}
    (authority : PeriodicTorus4FourierAuthority L Scalar Bound) →
  ∀ k l x →
  momentumCharacterDefinition authority (momentumAdd authority k l) x ≡
  multiplyScalar (operations authority)
    (momentumCharacterDefinition authority k x)
    (momentumCharacterDefinition authority l x)
momentumCharacterMultiplication = sourceMomentumCharacterMultiplication

momentumCharacterConjugation :
  ∀ {L Scalar Bound}
    (authority : PeriodicTorus4FourierAuthority L Scalar Bound) →
  ∀ k x →
  conjugateScalar (operations authority)
    (momentumCharacterDefinition authority k x)
  ≡ momentumCharacterDefinition authority (momentumNegate authority k) x
momentumCharacterConjugation = sourceMomentumCharacterConjugation

finiteFourierTransformDefinition :
  ∀ {L Scalar Bound} →
  PeriodicTorus4FourierAuthority L Scalar Bound →
  SiteField L Scalar → MomentumField L Scalar
finiteFourierTransformDefinition authority fld momentum =
  sumSites authority
    (λ site →
      multiplyScalar (operations authority)
        (conjugateScalar (operations authority)
          (momentumCharacterDefinition authority momentum site))
        (fld site))

finiteInverseFourierTransformDefinition :
  ∀ {L Scalar Bound} →
  PeriodicTorus4FourierAuthority L Scalar Bound →
  MomentumField L Scalar → SiteField L Scalar
finiteInverseFourierTransformDefinition authority fld site =
  multiplyScalar (operations authority)
    (normalizationScalar (operations authority))
    (sumMomenta authority
      (λ momentum →
        multiplyScalar (operations authority)
          (momentumCharacterDefinition authority momentum site)
          (fld momentum)))

------------------------------------------------------------------------
-- Standard theorem package, matched to the literal definitions above.
------------------------------------------------------------------------

record PeriodicTorus4FourierTheorems
    {L : Nat} {Scalar Bound : Set}
    (authority : PeriodicTorus4FourierAuthority L Scalar Bound) : Set₁ where
  field
    sourceCharacterOrthogonality : ∀ k l →
      sumSites authority
        (λ site →
          multiplyScalar (operations authority)
            (conjugateScalar (operations authority)
              (momentumCharacterDefinition authority k site))
            (momentumCharacterDefinition authority l site))
      ≡ multiplyScalar (operations authority)
          (cardinalityScalar (operations authority))
          (kronecker
            (periodicTorus4DecidableEquality L)
            (zeroScalar (operations authority))
            (oneScalar (operations authority))
            k l)

    sourceCharacterCompleteness : ∀ x y →
      sumMomenta authority
        (λ momentum →
          multiplyScalar (operations authority)
            (momentumCharacterDefinition authority momentum x)
            (conjugateScalar (operations authority)
              (momentumCharacterDefinition authority momentum y)))
      ≡ multiplyScalar (operations authority)
          (cardinalityScalar (operations authority))
          (kronecker
            (periodicTorus4DecidableEquality L)
            (zeroScalar (operations authority))
            (oneScalar (operations authority))
            x y)

    sourceFiniteFourierInversionLeft : ∀ fld site →
      finiteInverseFourierTransformDefinition authority
        (finiteFourierTransformDefinition authority fld)
        site
      ≡ fld site

    sourceFiniteFourierInversionRight : ∀ fld momentum →
      finiteFourierTransformDefinition authority
        (finiteInverseFourierTransformDefinition authority fld)
        momentum
      ≡ fld momentum

    sourceScalarFourierParseval : ∀ fld →
      scalarSiteNormSq authority fld ≡
      scalarMomentumNormSq authority
        (finiteFourierTransformDefinition authority fld)

open PeriodicTorus4FourierTheorems public

characterOrthogonality :
  ∀ {L Scalar Bound}
    {authority : PeriodicTorus4FourierAuthority L Scalar Bound} →
  PeriodicTorus4FourierTheorems authority → ∀ k l →
  sumSites authority
    (λ site →
      multiplyScalar (operations authority)
        (conjugateScalar (operations authority)
          (momentumCharacterDefinition authority k site))
        (momentumCharacterDefinition authority l site))
  ≡ multiplyScalar (operations authority)
      (cardinalityScalar (operations authority))
      (kronecker
        (periodicTorus4DecidableEquality L)
        (zeroScalar (operations authority))
        (oneScalar (operations authority))
        k l)
characterOrthogonality = sourceCharacterOrthogonality

characterCompleteness :
  ∀ {L Scalar Bound}
    {authority : PeriodicTorus4FourierAuthority L Scalar Bound} →
  PeriodicTorus4FourierTheorems authority → ∀ x y →
  sumMomenta authority
    (λ momentum →
      multiplyScalar (operations authority)
        (momentumCharacterDefinition authority momentum x)
        (conjugateScalar (operations authority)
          (momentumCharacterDefinition authority momentum y)))
  ≡ multiplyScalar (operations authority)
      (cardinalityScalar (operations authority))
      (kronecker
        (periodicTorus4DecidableEquality L)
        (zeroScalar (operations authority))
        (oneScalar (operations authority))
        x y)
characterCompleteness = sourceCharacterCompleteness

finiteFourierInversionLeft :
  ∀ {L Scalar Bound}
    {authority : PeriodicTorus4FourierAuthority L Scalar Bound} →
  PeriodicTorus4FourierTheorems authority → ∀ fld site →
  finiteInverseFourierTransformDefinition authority
    (finiteFourierTransformDefinition authority fld)
    site
  ≡ fld site
finiteFourierInversionLeft = sourceFiniteFourierInversionLeft

finiteFourierInversionRight :
  ∀ {L Scalar Bound}
    {authority : PeriodicTorus4FourierAuthority L Scalar Bound} →
  PeriodicTorus4FourierTheorems authority → ∀ fld momentum →
  finiteFourierTransformDefinition authority
    (finiteInverseFourierTransformDefinition authority fld)
    momentum
  ≡ fld momentum
finiteFourierInversionRight = sourceFiniteFourierInversionRight

scalarFourierParseval :
  ∀ {L Scalar Bound}
    {authority : PeriodicTorus4FourierAuthority L Scalar Bound} →
  PeriodicTorus4FourierTheorems authority → ∀ fld →
  scalarSiteNormSq authority fld ≡
  scalarMomentumNormSq authority
    (finiteFourierTransformDefinition authority fld)
scalarFourierParseval = sourceScalarFourierParseval

------------------------------------------------------------------------
-- Componentwise Fourier transform and inversion for positive-axis bonds.
------------------------------------------------------------------------

AxisSiteField : Nat → Set → Set
AxisSiteField L Scalar = AxisIndexedSiteField L Scalar

AxisMomentumField : Nat → Set → Set
AxisMomentumField L Scalar = Axis4 → MomentumField L Scalar

bondFourierTransform :
  ∀ {L Scalar Bound} →
  PeriodicTorus4FourierAuthority L Scalar Bound →
  AxisSiteField L Scalar → AxisMomentumField L Scalar
bondFourierTransform authority fld axis =
  finiteFourierTransformDefinition authority (fld axis)

bondInverseFourierTransform :
  ∀ {L Scalar Bound} →
  PeriodicTorus4FourierAuthority L Scalar Bound →
  AxisMomentumField L Scalar → AxisSiteField L Scalar
bondInverseFourierTransform authority fld axis =
  finiteInverseFourierTransformDefinition authority (fld axis)

bondFourierTransformComponentwise :
  ∀ {L Scalar Bound}
    (authority : PeriodicTorus4FourierAuthority L Scalar Bound) →
  ∀ fld axis momentum →
  bondFourierTransform authority fld axis momentum ≡
  finiteFourierTransformDefinition authority (fld axis) momentum
bondFourierTransformComponentwise authority fld axis momentum = refl

bondInverseFourierTransformComponentwise :
  ∀ {L Scalar Bound}
    (authority : PeriodicTorus4FourierAuthority L Scalar Bound) →
  ∀ fld axis site →
  bondInverseFourierTransform authority fld axis site ≡
  finiteInverseFourierTransformDefinition authority (fld axis) site
bondInverseFourierTransformComponentwise authority fld axis site = refl

bondFourierInversion :
  ∀ {L Scalar Bound}
    {authority : PeriodicTorus4FourierAuthority L Scalar Bound} →
  PeriodicTorus4FourierTheorems authority →
  ∀ fld axis site →
  bondInverseFourierTransform authority
    (bondFourierTransform authority fld)
    axis site
  ≡ fld axis site
bondFourierInversion theorems fld axis site =
  finiteFourierInversionLeft theorems (fld axis) site

axisComponentFourierParseval :
  ∀ {L Scalar Bound}
    {authority : PeriodicTorus4FourierAuthority L Scalar Bound} →
  PeriodicTorus4FourierTheorems authority →
  ∀ fld axis →
  scalarSiteNormSq authority (fld axis) ≡
  scalarMomentumNormSq authority
    (bondFourierTransform authority fld axis)
axisComponentFourierParseval theorems fld axis =
  scalarFourierParseval theorems (fld axis)

bondSiteNormSq :
  ∀ {L Scalar Bound} →
  PeriodicTorus4FourierAuthority L Scalar Bound →
  AxisSiteField L Scalar → Bound
bondSiteNormSq authority fld =
  sumBoundList (operations authority)
    (λ axis → scalarSiteNormSq authority (fld axis))
    (elements (cyclicIndexFinite four))

bondMomentumNormSq :
  ∀ {L Scalar Bound} →
  PeriodicTorus4FourierAuthority L Scalar Bound →
  AxisMomentumField L Scalar → Bound
bondMomentumNormSq authority fld =
  sumBoundList (operations authority)
    (λ axis → scalarMomentumNormSq authority (fld axis))
    (elements (cyclicIndexFinite four))

finiteAxisSumCommutesWithFourierSum :
  ∀ {L Scalar Bound}
    {authority : PeriodicTorus4FourierAuthority L Scalar Bound} →
  PeriodicTorus4FourierTheorems authority →
  ∀ fld axes →
  sumBoundList (operations authority)
    (λ axis → scalarSiteNormSq authority (fld axis)) axes
  ≡ sumBoundList (operations authority)
      (λ axis →
        scalarMomentumNormSq authority
          (bondFourierTransform authority fld axis)) axes
finiteAxisSumCommutesWithFourierSum theorems fld [] = refl
finiteAxisSumCommutesWithFourierSum {authority = authority}
  theorems fld (axis ∷ axes)
  rewrite axisComponentFourierParseval theorems fld axis
        | finiteAxisSumCommutesWithFourierSum theorems fld axes = refl

bondFieldFourierParseval :
  ∀ {L Scalar Bound}
    {authority : PeriodicTorus4FourierAuthority L Scalar Bound} →
  PeriodicTorus4FourierTheorems authority → ∀ fld →
  bondSiteNormSq authority fld ≡
  bondMomentumNormSq authority (bondFourierTransform authority fld)
bondFieldFourierParseval theorems fld =
  finiteAxisSumCommutesWithFourierSum theorems fld
    (elements (cyclicIndexFinite four))

fourierParsevalForBondFields :
  ∀ {L Scalar Bound}
    {authority : PeriodicTorus4FourierAuthority L Scalar Bound} →
  PeriodicTorus4FourierTheorems authority → ∀ fld →
  bondSiteNormSq authority fld ≡
  bondMomentumNormSq authority (bondFourierTransform authority fld)
fourierParsevalForBondFields = bondFieldFourierParseval

scaledScalarParseval :
  ∀ {L Scalar Bound}
    {authority : PeriodicTorus4FourierAuthority L Scalar Bound} →
  PeriodicTorus4FourierTheorems authority →
  ∀ scalar fld →
  scaleBound (operations authority) scalar
    (scalarSiteNormSq authority fld)
  ≡ scaleBound (operations authority) scalar
      (scalarMomentumNormSq authority
        (finiteFourierTransformDefinition authority fld))
scaledScalarParseval {authority = authority} theorems scalar fld =
  cong (scaleBound (operations authority) scalar)
    (scalarFourierParseval theorems fld)

scaledBondParseval :
  ∀ {L Scalar Bound}
    {authority : PeriodicTorus4FourierAuthority L Scalar Bound} →
  PeriodicTorus4FourierTheorems authority →
  ∀ scalar fld →
  scaleBound (operations authority) scalar
    (bondSiteNormSq authority fld)
  ≡ scaleBound (operations authority) scalar
      (bondMomentumNormSq authority
        (bondFourierTransform authority fld))
scaledBondParseval {authority = authority} theorems scalar fld =
  cong (scaleBound (operations authority) scalar)
    (bondFieldFourierParseval theorems fld)

latticeSpacingNormalizationParseval :
  ∀ {L Scalar Bound}
    {authority : PeriodicTorus4FourierAuthority L Scalar Bound} →
  PeriodicTorus4FourierTheorems authority →
  ∀ latticeNormalization fld →
  scaleBound (operations authority) latticeNormalization
    (bondSiteNormSq authority fld)
  ≡ scaleBound (operations authority) latticeNormalization
      (bondMomentumNormSq authority
        (bondFourierTransform authority fld))
latticeSpacingNormalizationParseval = scaledBondParseval

periodicTorus4FourierDefinitionsLevel : ProofLevel
periodicTorus4FourierDefinitionsLevel = machineChecked

finiteAbelianFourierTheoremsLevel : ProofLevel
finiteAbelianFourierTheoremsLevel = standardImported

bondFourierConsequencesLevel : ProofLevel
bondFourierConsequencesLevel = machineChecked
