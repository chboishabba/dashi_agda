module DASHI.Moonshine.OggSSPP3F9ExtensionQuotientSourceExact where

------------------------------------------------------------------------
-- p=3 F9 EXTENSION-COORDINATE MARKED SOURCE
--
-- DASHI FORMAL RECONSTRUCTION
--
-- This module inhabits P3MarkedFrobeniusSource with the exact quotient already
-- constructed from the finite F9/F3 Frobenius model:
--
--     (a,b) |-> b,       Frobenius(a,b) = (a,-b).
--
-- On the quotient this is exactly the canonical three-state involution
--
--     0 fixed,  +/- exchanged.
--
-- Hence every field of the repository source socket is constructively paid.
--
-- ATTRIBUTION FIREWALL
--
-- "flipIsArithmeticFrobenius = true" means the flip IS the induced Frobenius
-- of THIS formally reconstructed F9 quotient.  It does NOT claim that an
-- external source identifies this quotient with a classical marked
-- supersingular moduli problem.  That external-identification statement remains
-- separately false/uninhabited below.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.OggSSPP3F9ExtensionQuotientCandidateExact as Candidate
import DASHI.Moonshine.OggSSPSmallCharacteristicArithmeticSourceSocketExact as Socket
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

canonicalP3MarkedFrobeniusSource :
  Socket.P3MarkedFrobeniusSource
canonicalP3MarkedFrobeniusSource =
  record
    { MarkedState =
        Candidate.P3ExtensionQuotientState
    ; action =
        Candidate.quotientAction
    ; candidateOrbits =
        Candidate.quotientOrbits
    ; coarseJ =
        Candidate.quotientCoarseJ
    ; coarseJConstant =
        Candidate.quotientCoarseJConstant
    ; markedWitness =
        Candidate.markedWitness
    ; frobeniusMovesMarkedWitness =
        Candidate.markedWitnessMoves
    ; flipIsArithmeticFrobenius =
        true
    ; flipIsArithmeticFrobeniusIsTrue =
        refl
    }

------------------------------------------------------------------------
-- The source is inhabited as a formal arithmetic reconstruction.
------------------------------------------------------------------------

p3MarkedSourceCarrierIsExtensionQuotient :
  Socket.P3MarkedFrobeniusSource.MarkedState
    canonicalP3MarkedFrobeniusSource
  ≡ Candidate.P3ExtensionQuotientState
p3MarkedSourceCarrierIsExtensionQuotient = refl

p3MarkedSourceUsesInducedF9Frobenius :
  Socket.P3MarkedFrobeniusSource.flipIsArithmeticFrobenius
    canonicalP3MarkedFrobeniusSource
  ≡ true
p3MarkedSourceUsesInducedF9Frobenius = refl

------------------------------------------------------------------------
-- External moduli identification remains a distinct obligation.
------------------------------------------------------------------------

data ExternalClassicalModuliIdentifiesP3ExtensionQuotient : Set where

externalClassicalModuliIdentificationStillOpen :
  ExternalClassicalModuliIdentifiesP3ExtensionQuotient -> ⊥
externalClassicalModuliIdentificationStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryFormalReconstruction

record P3ExtensionQuotientSourceBoundary : Set where
  constructor p3-extension-quotient-source-boundary
  field
    sourceSocketInhabited : Bool
    inducedF9FrobeniusUsed : Bool
    exactTwoOrbitPresentationUsed : Bool
    movedWitnessUsed : Bool
    coarseJConstantUsed : Bool
    repositoryFormalReconstruction : Bool
    externalClassicalModuliIdentificationPaid : Bool
    externalSourceCreditedWithDASHIQuotient : Bool

canonicalP3ExtensionQuotientSourceBoundary :
  P3ExtensionQuotientSourceBoundary
canonicalP3ExtensionQuotientSourceBoundary =
  p3-extension-quotient-source-boundary
    true true true true true true false false
