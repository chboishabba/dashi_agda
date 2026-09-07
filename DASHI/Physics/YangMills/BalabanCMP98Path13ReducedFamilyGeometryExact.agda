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
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed

record ReducedPath13FamilyGeometry (CoarseField : Set) : Set₁ where
  field
    selectedPhysical :
      PathTarget.SelectedPhysicalBackground13Instantiation
        CoarseField Lie.SU2LieAlgebra

    radiusSixWalkAgreement :
      Bijection.CenteredTorusWalkAgreementCertificate R158.sourceRadius

open ReducedPath13FamilyGeometry public

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

reducedMinusEmbeddingCentreIsBondSource :
  ∀ {CoarseField}
    (reduced : ReducedPath13FamilyGeometry CoarseField)
    bond step →
  Embed.embeddingCentre
    (Family.minusEmbeddingFor (asPath13FamilyGeometry reduced) bond step)
  ≡ Carrier.first bond
reducedMinusEmbeddingCentreIsBondSource reduced bond step = refl

reducedFamilyBackgroundIsSelectedPath13 :
  ∀ {CoarseField}
    (reduced : ReducedPath13FamilyGeometry CoarseField) →
  Family.familyBackground (asPath13FamilyGeometry reduced)
  ≡ PathTarget.path13Background (selectedPhysical reduced)
reducedFamilyBackgroundIsSelectedPath13 reduced = refl

cmp98Path13ReducedFamilyGeometryCompilerLevel : ProofLevel
cmp98Path13ReducedFamilyGeometryCompilerLevel = machineChecked

cmp98Path13BondCenteredEmbeddingFamilyPrunedLevel : ProofLevel
cmp98Path13BondCenteredEmbeddingFamilyPrunedLevel = machineChecked

-- The remaining geometry-side source receipt is one finite radius-six
-- walk-agreement certificate, not a choice of embedding at each bond.
literalCMP98Path13RadiusSixWalkAgreementLevel : ProofLevel
literalCMP98Path13RadiusSixWalkAgreementLevel = conditional
