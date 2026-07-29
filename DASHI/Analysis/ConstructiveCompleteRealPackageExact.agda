module DASHI.Analysis.ConstructiveCompleteRealPackageExact where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Analysis.ConstructiveRealCapabilityHierarchyExact as Capability
import DASHI.Analysis.ConstructiveRealTransportCapabilitiesExact as Transport
import DASHI.Analysis.ConstructiveRealCategoricityExact as Categoricity
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Stable packaged constructive-real capability surface.
--
-- Herman Geuvers and Milad Niqui,
-- "Constructive Reals in Coq: Axioms and Categoricity",
-- Types for Proofs and Programs, LNCS 2277 (2002), 79--95.
-- DOI: 10.1007/3-540-45842-5_6.
--
-- Rocq/Coq standard-library precedent:
--   Coq.Reals.Abstract.ConstructiveReals
--   Coq.Reals.ConstructiveRealsMorphisms
-- Software documentation; no DOI.
------------------------------------------------------------------------

record ConstructiveCompleteRealPackage : Set₂ where
  field
    packageName : String
    backend : Spine.ConstructiveRealBackend

    constructiveField :
      Capability.ConstructiveOrderedFieldCapability (Spine.real backend)
    rationals :
      Capability.RationalEmbeddingStructure (Spine.real backend)
    rationalDensity :
      Capability.RationalDensityStructure (Spine.real backend) rationals
    naturalMajorization :
      Capability.NaturalMajorizationStructure (Spine.real backend)
    densityMajorizationBridge :
      Capability.DensityMajorizationBridge
        (Spine.real backend) rationals rationalDensity naturalMajorization

    effectiveConvergence :
      Capability.EffectiveConvergenceStructure (Spine.real backend)
    effectiveLogicalOrder :
      Transport.EffectiveLogicalOrderView (Spine.real backend)

open ConstructiveCompleteRealPackage public

packageCarrier : ConstructiveCompleteRealPackage → Set
packageCarrier package = Spine.Carrier (Spine.real (backend package))

packageArchimedeanCeiling :
  (package : ConstructiveCompleteRealPackage) →
  (value : packageCarrier package) →
  Σ Nat
    (λ bound →
      Spine._<_ (Spine.real (backend package)) value
        (Capability.fromNat (naturalMajorization package) bound))
packageArchimedeanCeiling package =
  Capability.archimedeanCeiling (densityMajorizationBridge package)

record PackagedConstructiveRealMorphism
    (Source Target : ConstructiveCompleteRealPackage) : Set₂ where
  field
    minimal :
      Capability.ConstructiveRealHomomorphism
        (Spine.real (backend Source))
        (Spine.real (backend Target))
        (constructiveField Source)
        (constructiveField Target)

    CommonQ : Set
    decodeSource : CommonQ → Capability.Q (rationals Source)
    decodeTarget : CommonQ → Capability.Q (rationals Target)

    rationalArchimedean :
      Transport.RationalArchimedeanMorphism
        (rationals Source) (rationals Target)
        CommonQ decodeSource decodeTarget minimal

    derivedTransport :
      Transport.MinimalHomomorphismTransportDerivation minimal

    effectiveModuli :
      Transport.ModulusTransportCapability
        minimal
        (effectiveConvergence Source)
        (effectiveConvergence Target)

open PackagedConstructiveRealMorphism public

record PackagedCategoricityAuthority
    (Left Right : ConstructiveCompleteRealPackage) : Set₂ where
  field
    categoricity :
      Categoricity.ConstructiveRealCategoricityAuthority
        (Spine.real (backend Left))
        (Spine.real (backend Right))

    forwardPackageMorphism : PackagedConstructiveRealMorphism Left Right
    backwardPackageMorphism : PackagedConstructiveRealMorphism Right Left

    forwardMinimalIsCanonical : ∀ value → Set
    backwardMinimalIsCanonical : ∀ value → Set
    packageMorphismUnique : Set

open PackagedCategoricityAuthority public

constructiveCompleteRealPackageLevel : ProofLevel
constructiveCompleteRealPackageLevel = machineChecked

packageArchimedeanCeilingLevel : ProofLevel
packageArchimedeanCeilingLevel = machineChecked

packagedMorphismAndCategoricityInputsLevel : ProofLevel
packagedMorphismAndCategoricityInputsLevel = conditional
