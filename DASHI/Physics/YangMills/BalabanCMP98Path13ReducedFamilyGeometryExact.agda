{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13ReducedFamilyGeometryExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanPath13SelectedPhysicalBackgroundTargetExact as PathTarget
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredTorusBijectionExact as Bijection
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Path13TwoCarrierSourceFamilyExact as Family
import DASHI.Physics.YangMills.BalabanPath13CanonicalBondCenteredEmbeddingExact as Canonical
import DASHI.Physics.YangMills.BalabanPath13RadiusSixWalkAgreementExact as RadiusSix
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed

record ReducedPath13FamilyGeometry (CoarseField : Set) : Set₁ where
  field
    selectedPhysical :
      PathTarget.SelectedPhysicalBackground13Instantiation
        CoarseField Lie.SU2LieAlgebra

    radiusSixWalkAgreement :
      Bijection.CenteredTorusWalkAgreementCertificate R158.sourceRadius

open ReducedPath13FamilyGeometry public

-- The finite radius-six geometry is now constructed internally.  A caller that
-- already has the selected Path13 physical/variational background no longer
-- supplies any additional embedding or walk-agreement receipt.
canonicalReducedPath13FamilyGeometry :
  ∀ {CoarseField} →
  PathTarget.SelectedPhysicalBackground13Instantiation
    CoarseField Lie.SU2LieAlgebra →
  ReducedPath13FamilyGeometry CoarseField
canonicalReducedPath13FamilyGeometry selected = record
  { selectedPhysical = selected
  ; radiusSixWalkAgreement = RadiusSix.radiusSixWalkAgreement
  }

asPath13FamilyGeometry :
  ∀ {CoarseField} →
  ReducedPath13FamilyGeometry CoarseField →
  Family.Path13FamilyGeometry CoarseField
asPath13FamilyGeometry reduced = record
  { Family.Path13FamilyGeometry.selectedPhysical = selectedPhysical reduced
  ; Family.Path13FamilyGeometry.minusEmbeddingFor =
      λ bond step →
        Canonical.canonicalEmbeddingAtSite
          (radiusSixWalkAgreement reduced)
          (Carrier.first bond)
  }

canonicalPath13FamilyGeometry :
  ∀ {CoarseField} →
  PathTarget.SelectedPhysicalBackground13Instantiation
    CoarseField Lie.SU2LieAlgebra →
  Family.Path13FamilyGeometry CoarseField
canonicalPath13FamilyGeometry selected =
  asPath13FamilyGeometry (canonicalReducedPath13FamilyGeometry selected)

reducedMinusEmbeddingCentreIsBondSource :
  ∀ {CoarseField}
    (reduced : ReducedPath13FamilyGeometry CoarseField)
    bond step →
  Embed.embeddingCentre
    (Family.minusEmbeddingFor (asPath13FamilyGeometry reduced) bond step)
  ≡ Carrier.first bond
reducedMinusEmbeddingCentreIsBondSource reduced bond step = refl

canonicalMinusEmbeddingCentreIsBondSource :
  ∀ {CoarseField}
    (selected : PathTarget.SelectedPhysicalBackground13Instantiation
      CoarseField Lie.SU2LieAlgebra)
    bond step →
  Embed.embeddingCentre
    (Family.minusEmbeddingFor (canonicalPath13FamilyGeometry selected) bond step)
  ≡ Carrier.first bond
canonicalMinusEmbeddingCentreIsBondSource selected bond step = refl

reducedFamilyBackgroundIsSelectedPath13 :
  ∀ {CoarseField}
    (reduced : ReducedPath13FamilyGeometry CoarseField) →
  Family.familyBackground (asPath13FamilyGeometry reduced)
  ≡ PathTarget.path13Background (selectedPhysical reduced)
reducedFamilyBackgroundIsSelectedPath13 reduced = refl

canonicalFamilyBackgroundIsSelectedPath13 :
  ∀ {CoarseField}
    (selected : PathTarget.SelectedPhysicalBackground13Instantiation
      CoarseField Lie.SU2LieAlgebra) →
  Family.familyBackground (canonicalPath13FamilyGeometry selected)
  ≡ PathTarget.path13Background selected
canonicalFamilyBackgroundIsSelectedPath13 selected = refl

cmp98Path13ReducedFamilyGeometryCompilerLevel : ProofLevel
cmp98Path13ReducedFamilyGeometryCompilerLevel = machineChecked

cmp98Path13BondCenteredEmbeddingFamilyPrunedLevel : ProofLevel
cmp98Path13BondCenteredEmbeddingFamilyPrunedLevel = machineChecked

cmp98Path13RadiusSixWalkAgreementLevel : ProofLevel
cmp98Path13RadiusSixWalkAgreementLevel = RadiusSix.path13RadiusSixWalkAgreementLevel

literalCMP98Path13RadiusSixWalkAgreementLevel : ProofLevel
literalCMP98Path13RadiusSixWalkAgreementLevel = machineChecked
