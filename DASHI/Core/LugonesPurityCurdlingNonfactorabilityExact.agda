module DASHI.Core.LugonesPurityCurdlingNonfactorabilityExact where

------------------------------------------------------------------------
-- LUGONES PURITY / IMPURITY / CURDLING NONFACTORABILITY BRIDGE
--
-- SOURCE CONTEXT
--
-- Maria Lugones, "Purity, Impurity, and Separation", Signs 19(2), 1994.
-- DOI 10.1086/494893.
--
-- Lugones motivates critique of purity, separation and hidden-unity accounts of
-- multiplicity.  The Nat-valued response surface and rectangle obstruction are
-- DASHI constructions, reusing BinaryInteractionNonseparabilityExact; Lugones
-- is not credited with that algebra.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.BinaryInteractionNonseparabilityExact as Interaction

------------------------------------------------------------------------
-- Finite impurity/curdling regression.
--
-- Each endpoint alone carries no joint code, while heterogeneous pairing does.
-- This supplies an exact counterexample to reconstruction as endpoint-only
-- additive potentials.
------------------------------------------------------------------------

data MultiplicityAspect : Set where
  aspectA aspectB : MultiplicityAspect

curdledResponse : MultiplicityAspect → MultiplicityAspect → Nat
curdledResponse aspectA aspectA = 0
curdledResponse aspectA aspectB = 1
curdledResponse aspectB aspectA = 1
curdledResponse aspectB aspectB = 0

curdledSurface : Interaction.BinaryNatSurface
curdledSurface =
  Interaction.binary-nat-surface
    MultiplicityAspect MultiplicityAspect curdledResponse
    "Finite Lugones-calibrated impurity/curdling regression; DASHI response code, not empirical scale."

curdledRectangleObstruction :
  Interaction.RectangleObstruction curdledSurface
curdledRectangleObstruction =
  Interaction.rectangle-obstruction aspectA aspectB aspectA aspectB (λ ())

curdledRankOneObstruction :
  Interaction.RankOneMinorObstruction curdledSurface
curdledRankOneObstruction =
  Interaction.rank-one-minor-obstruction aspectA aspectB aspectA aspectB (λ ())

curdledStrongInteraction :
  Interaction.StrongBinaryInteractionAdmission curdledSurface
curdledStrongInteraction =
  Interaction.strong-binary-interaction-admission
    curdledRectangleObstruction curdledRankOneObstruction

curdledMultiplicityIsNotEndpointAdditive :
  Interaction.NonseparableAdditiveInteraction curdledSurface
curdledMultiplicityIsNotEndpointAdditive =
  Interaction.strongAdmissionImpliesAdditiveNonseparability
    curdledStrongInteraction

------------------------------------------------------------------------
-- Purity is represented as a factorisation hypothesis, not as the default
-- meaning of multiplicity.
------------------------------------------------------------------------

PureEndpointFactorisation : Set₁
PureEndpointFactorisation =
  Interaction.EndpointAdditivelySeparable curdledSurface

curdledWitnessBlocksPureEndpointFactorisation : PureEndpointFactorisation → ⊥
curdledWitnessBlocksPureEndpointFactorisation =
  curdledMultiplicityIsNotEndpointAdditive

record LugonesPurityBoundary : Set where
  constructor lugones-purity-boundary
  field
    pluralityImpliesIndependentPureComponents : Bool
    pluralityImpliesIndependentPureComponentsIsFalse :
      pluralityImpliesIndependentPureComponents ≡ false
    fragmentationProvesUnderlyingUnity : Bool
    fragmentationProvesUnderlyingUnityIsFalse :
      fragmentationProvesUnderlyingUnity ≡ false
    nonseparabilityProvesLugonesSocialTheory : Bool
    nonseparabilityProvesLugonesSocialTheoryIsFalse :
      nonseparabilityProvesLugonesSocialTheory ≡ false
    natResponseIsEmpiricalIdentityScale : Bool
    natResponseIsEmpiricalIdentityScaleIsFalse :
      natResponseIsEmpiricalIdentityScale ≡ false

canonicalLugonesPurityBoundary : LugonesPurityBoundary
canonicalLugonesPurityBoundary =
  lugones-purity-boundary false refl false refl false refl false refl
