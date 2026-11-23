module DASHI.Physics.YangMills.BalabanPeriodicFourierNormalizationMatching where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Fourier

------------------------------------------------------------------------
-- Exact normalization matching for the literal periodic transform.
--
-- Character orthogonality and finite Fourier inversion are standard finite
-- harmonic analysis.  The repository-specific obligation is not merely to cite
-- that theorem, but to check that the transform convention, |Lambda| factor and
-- lattice-spacing weight agree with the physical bond norms.  This module makes
-- those equalities explicit and derives the physical Parseval identity by
-- rewriting only.
------------------------------------------------------------------------

record PeriodicFourierNormalizationMatch
    {L : Nat} {Scalar Bound : Set}
    (authority : PeriodicTorus4FourierAuthority L Scalar Bound)
    (theorems : PeriodicTorus4FourierTheorems authority) : Set₁ where
  field
    latticeSpacing latticeSpacingFourthPower siteCardinality
      inverseSiteCardinality physicalWeight : Scalar

    multiplyAssociative : ∀ a b c →
      multiplyScalar (operations authority)
        (multiplyScalar (operations authority) a b) c
      ≡ multiplyScalar (operations authority) a
          (multiplyScalar (operations authority) b c)

    inverseCardinalityNormalization :
      multiplyScalar (operations authority)
        inverseSiteCardinality siteCardinality
      ≡ oneScalar (operations authority)

    transformNormalizationMatchesInverseCardinality :
      normalizationScalar (operations authority) ≡ inverseSiteCardinality

    transformCardinalityMatchesTorusCardinality :
      cardinalityScalar (operations authority) ≡ siteCardinality

    latticeSpacingFourthPowerDefinition :
      latticeSpacingFourthPower ≡
      multiplyScalar (operations authority) latticeSpacing
        (multiplyScalar (operations authority) latticeSpacing
          (multiplyScalar (operations authority) latticeSpacing latticeSpacing))

    physicalWeightDefinition : physicalWeight ≡ latticeSpacingFourthPower

    physicalBondSiteNorm : AxisSiteField L Scalar → Bound
    physicalBondMomentumNorm : AxisMomentumField L Scalar → Bound

    physicalBondSiteNormDefinition : ∀ fld →
      physicalBondSiteNorm fld ≡
      scaleBound (operations authority) physicalWeight
        (bondSiteNormSq authority fld)

    physicalBondMomentumNormDefinition : ∀ fld →
      physicalBondMomentumNorm fld ≡
      scaleBound (operations authority) physicalWeight
        (bondMomentumNormSq authority fld)

open PeriodicFourierNormalizationMatch public

physicalBondFourierParseval :
  ∀ {L : Nat} {Scalar Bound : Set}
    {authority : PeriodicTorus4FourierAuthority L Scalar Bound}
    {theorems : PeriodicTorus4FourierTheorems authority} →
    (matching : PeriodicFourierNormalizationMatch authority theorems) →
    ∀ fld →
    physicalBondSiteNorm matching fld ≡
    physicalBondMomentumNorm matching
      (bondFourierTransform authority fld)
physicalBondFourierParseval {authority = authority} {theorems = theorems}
  matching fld
  rewrite physicalBondSiteNormDefinition matching fld
        | physicalBondMomentumNormDefinition matching
            (bondFourierTransform authority fld) =
  latticeSpacingNormalizationParseval theorems
    (physicalWeight matching) fld

literalTransformUsesInverseCardinality :
  ∀ {L : Nat} {Scalar Bound : Set}
    {authority : PeriodicTorus4FourierAuthority L Scalar Bound}
    {theorems : PeriodicTorus4FourierTheorems authority} →
    (matching : PeriodicFourierNormalizationMatch authority theorems) →
    normalizationScalar (operations authority) ≡
    inverseSiteCardinality matching
literalTransformUsesInverseCardinality =
  transformNormalizationMatchesInverseCardinality

literalCharacterSumUsesTorusCardinality :
  ∀ {L : Nat} {Scalar Bound : Set}
    {authority : PeriodicTorus4FourierAuthority L Scalar Bound}
    {theorems : PeriodicTorus4FourierTheorems authority} →
    (matching : PeriodicFourierNormalizationMatch authority theorems) →
    cardinalityScalar (operations authority) ≡ siteCardinality matching
literalCharacterSumUsesTorusCardinality =
  transformCardinalityMatchesTorusCardinality

periodicFourierNormalizationMatchingLevel : ProofLevel
periodicFourierNormalizationMatchingLevel = machineChecked

periodicLiteralFiniteFourierTheoremLevel : ProofLevel
periodicLiteralFiniteFourierTheoremLevel = standardImported
