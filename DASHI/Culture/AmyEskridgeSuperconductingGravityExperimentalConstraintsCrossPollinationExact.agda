module DASHI.Culture.AmyEskridgeSuperconductingGravityExperimentalConstraintsCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Culture.AmyEskridgeLiTorrSourceConstitutiveCrossPollinationExact as X
import DASHI.Physics.ExoticGravity.SuperconductingGravityExperimentalConstraintRegistryExact as E
import DASHI.Physics.ExoticGravity.SuperconductingSourceConstitutiveEvidenceBidiExact as B

------------------------------------------------------------------------
-- ESKRIDGE x PUBLIC EXPERIMENTAL CONSTRAINTS
--
-- Public advocacy and historical mechanism interest are not promoted by later
-- experimental claims.  The experimental literature instead constrains which
-- mechanism families remain admissible and where the next acquisition must go.
------------------------------------------------------------------------

record ExperimentalCrossPollination : Set where
  constructor experimental-cross-pollination
  field
    nullReplicationsImportedAsConstraints : Bool
    nullReplicationsImportedAsConstraintsIsTrue :
      nullReplicationsImportedAsConstraints ≡ true

    artifactAttributionsImportedAsConstraints : Bool
    artifactAttributionsImportedAsConstraintsIsTrue :
      artifactAttributionsImportedAsConstraints ≡ true

    transitionMismatchImportedAsDiscriminator : Bool
    transitionMismatchImportedAsDiscriminatorIsTrue :
      transitionMismatchImportedAsDiscriminator ≡ true

    largeEnhancementModelsConstrained : Bool
    largeEnhancementModelsConstrainedIsTrue :
      largeEnhancementModelsConstrained ≡ true

    experimentalConstraintsProveEskridgeWrong : Bool
    experimentalConstraintsProveEskridgeWrongIsFalse :
      experimentalConstraintsProveEskridgeWrong ≡ false

    experimentalConstraintsEstablishNonzeroEtaC : Bool
    experimentalConstraintsEstablishNonzeroEtaCIsFalse :
      experimentalConstraintsEstablishNonzeroEtaC ≡ false

canonicalExperimentalCrossPollination : ExperimentalCrossPollination
canonicalExperimentalCrossPollination = experimental-cross-pollination
  true refl
  true refl
  true refl
  true refl
  false refl
  false refl

experimentalFrontier : B.EvidenceLeaf
experimentalFrontier = B.currentFirstOpenEvidenceLeaf
