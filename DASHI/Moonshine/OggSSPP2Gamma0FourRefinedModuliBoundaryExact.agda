module DASHI.Moonshine.OggSSPP2Gamma0FourRefinedModuliBoundaryExact where

------------------------------------------------------------------------
-- p=2, N=4: NON-SQUAREFREE GAMMA_0 MODULI BOUNDARY
--
-- EXTERNAL SOURCE
--
-- Kestutis Cesnavicius,
-- "A modular description of X_0(n)", arXiv:1511.07475.
-- DOI: 10.48550/arXiv.1511.07475.
--
-- Source fact used here:
-- for nonsquarefree n, the naive compactified moduli stack of generalized
-- elliptic curves with an ample cyclic subgroup of order n does not agree at
-- the cusps with the Deligne--Rapoport Gamma_0(n) stack.  A refined moduli
-- problem is needed to recover X_0(n) integrally.
--
-- DASHI consequence for n=4:
-- the finite-flat cyclic subgroup socket is a lawful INTERIOR elliptic-curve
-- source interface, but it must not be promoted by naming into the complete
-- compactified X_0(4) moduli stack.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Moonshine.OggSSPP2Gamma0FourMarkedSubgroupSchemeSourceExact as Interior
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

level : Nat
level = 4

levelIsNotSquarefree : Bool
levelIsNotSquarefree = true

data Gamma0FourModuliScope : Set where
  interiorEllipticFiniteFlatSubgroup :
    Gamma0FourModuliScope

  naiveCompactifiedAmpleCyclicSubgroup :
    Gamma0FourModuliScope

  refinedDeligneRapoportCompactification :
    Gamma0FourModuliScope

record RefinedGamma0FourCompactifiedSource : Set₁ where
  field
    interiorDatum :
      Interior.Gamma0FourFiniteFlatDatum

    compactifiedState : Set

    scope :
      Gamma0FourModuliScope

    scopeIsRefined :
      scope ≡ refinedDeligneRapoportCompactification

    cuspRefinementConstructed : Bool
    cuspRefinementConstructedIsTrue :
      cuspRefinementConstructed ≡ true

open RefinedGamma0FourCompactifiedSource public

data InteriorDatumIsFullCompactification : Set where
data NaiveAmpleCyclicStackEqualsDRAtLevelFour : Set where

interiorDatumDoesNotCreateFullCompactification :
  InteriorDatumIsFullCompactification -> ⊥
interiorDatumDoesNotCreateFullCompactification ()

naiveAmpleCyclicStackDoesNotBecomeDRByNaming :
  NaiveAmpleCyclicStackEqualsDRAtLevelFour -> ⊥
naiveAmpleCyclicStackDoesNotBecomeDRByNaming ()

sourceCitation : String
sourceCitation =
  "K. Cesnavicius, A modular description of X_0(n), arXiv:1511.07475, DOI 10.48550/arXiv.1511.07475"

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryNewExtension

record Gamma0FourRefinedModuliBoundary : Set where
  constructor gamma0-four-refined-moduli-boundary
  field
    levelFourRecognizedAsNonsquarefree : Bool
    interiorFiniteFlatSubgroupSocketRetained : Bool
    naiveCompactifiedCyclicSubgroupPromotedToFullX0Four : Bool
    refinedCompactificationRequiredAtCusps : Bool
    arithmeticInteriorSourceConstructed : Bool
    refinedCompactifiedSourceConstructed : Bool

canonicalGamma0FourRefinedModuliBoundary :
  Gamma0FourRefinedModuliBoundary
canonicalGamma0FourRefinedModuliBoundary =
  gamma0-four-refined-moduli-boundary
    true true false true false false
