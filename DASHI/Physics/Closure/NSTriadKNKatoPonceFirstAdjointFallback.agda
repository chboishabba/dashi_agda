module DASHI.Physics.Closure.NSTriadKNKatoPonceFirstAdjointFallback where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator estimates and the Euler and Navier-Stokes equations".
-- Venue/year: Communications on Pure and Applied Mathematics 41 (1988),
-- issue 7, pages 891--907.
-- DOI: 10.1002/cpa.3160410704.
-- Uses: the fractional Leibniz/commutator mechanism controlling a derivative
-- of a product or a multiplier commutator by one differentiated factor and
-- one L-infinity factor.
-- Relationship: this is the verified peer-reviewed source for the Stage-3
-- commutator fallback.  The source theorem is not silently identified with the
-- repository's periodic orbit/helicity kernel: periodic multiplier matching,
-- shell localization, endpoint exponents, and cutoff-independent transport
-- remain explicit obligations.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record KatoPonceCommutatorCarrier
    {f n s : Level} : Set (lsuc (f ⊔ n ⊔ s)) where
  field
    Function : Set f
    Norm : Set n
    Smoothness : Set s

    lambda : Smoothness → Function → Function
    multiplyFunctions : Function → Function → Function
    subtractFunctions : Function → Function → Function

    l2Norm linfinityNorm : Function → Norm
    addNorm multiplyNorm leqNorm : Set n

open KatoPonceCommutatorCarrier public

record KatoPonceRepositoryInstantiationCutset
    {f n s : Level}
    (C : KatoPonceCommutatorCarrier {f} {n} {s}) :
    Set (lsuc (f ⊔ n ⊔ s)) where
  field
    sourceCommutatorStatementMatched : Set
    selectedAlphaMatchesStage3Weight : Set
    periodicTorusVersionAvailable : Set
    dyadicMultiplierDifferenceDerived : Set
    firstAdjointKernelWrittenAsCommutator : Set
    lowFrequencyFactorPlacedInLInfinity : Set
    highFrequencyDerivativePaidInL2 : Set
    fiveHalvesBelowSBelowThreeAdmissible : Set

    orbitNormalizationPreserved : Set
    helicityResolutionPreserved : Set
    directionWeightPreserved : Set
    constantIndependentOfGalerkinCutoff : Set

open KatoPonceRepositoryInstantiationCutset public

katoPonceBibliographyVerified : Bool
katoPonceBibliographyVerified = true

katoPonceBibliographyVerifiedIsTrue :
  katoPonceBibliographyVerified ≡ true
katoPonceBibliographyVerifiedIsTrue = refl

katoPoncePromotedAsFallbackMechanism : Bool
katoPoncePromotedAsFallbackMechanism = true

katoPoncePromotedAsFallbackMechanismIsTrue :
  katoPoncePromotedAsFallbackMechanism ≡ true
katoPoncePromotedAsFallbackMechanismIsTrue = refl

katoPonceSelectedAsPrimaryFirstAdjointRoute : Bool
katoPonceSelectedAsPrimaryFirstAdjointRoute = false

katoPonceSelectedAsPrimaryFirstAdjointRouteIsFalse :
  katoPonceSelectedAsPrimaryFirstAdjointRoute ≡ false
katoPonceSelectedAsPrimaryFirstAdjointRouteIsFalse = refl

repositoryKatoPonceInstantiationClosed : Bool
repositoryKatoPonceInstantiationClosed = false

repositoryKatoPonceInstantiationClosedIsFalse :
  repositoryKatoPonceInstantiationClosed ≡ false
repositoryKatoPonceInstantiationClosedIsFalse = refl
