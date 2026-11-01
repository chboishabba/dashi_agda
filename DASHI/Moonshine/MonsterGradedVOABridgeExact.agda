module DASHI.Moonshine.MonsterGradedVOABridgeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Igor Frenkel, James Lepowsky and Arne Meurman,
-- "Vertex Operator Algebras and the Monster", Pure and Applied Mathematics
-- 134, Academic Press, 1988.  No DOI is asserted here.
--
-- Richard E. Borcherds,
-- "Monstrous moonshine and monstrous Lie superalgebras",
-- Inventiones Mathematicae 109 (1992), 405--444.
-- DOI: 10.1007/BF01232032.
--
-- John F. R. Duncan, Michael J. Griffin and Ken Ono,
-- "Moonshine", Research in the Mathematical Sciences 2, 11 (2015).
-- DOI: 10.1186/s40687-015-0029-6.
--
-- DASHI CONTRIBUTION
--
-- Cross-pollinate the new graded-VOA obligation surface with the repository's
-- existing graded representation, exact character table, first J-coefficient
-- and McKay--Thompson closure modules.  The exact theorem available locally is
-- the identity graded-trace coefficient/dimension equality inherited from the
-- generic VOA trace bridge.
--
-- Construction of V^natural, identification of its full automorphism group
-- with the Monster, VOA rationality/C2-cofiniteness, modularity and genus zero
-- remain separate proof fields.  The arithmetic identity 196884=1+196883 does
-- not construct the VOA or prove monstrous moonshine.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Moonshine.GradedRepresentation as GR
import DASHI.Moonshine.GradedVertexOperatorAlgebraBoundary as GVOA
import DASHI.Moonshine.JCoefficientCharacterBridge as J
import DASHI.Moonshine.MonsterCharacterTableExact as MCT

record MonsterGradedVOABridge (Monster K : Set) : Setω where
  field
    monsterGroup : GR.Group Monster
    voaAction : GVOA.VOAWithGroupAction Monster K
    groupAgreement : GVOA.group voaAction ≡ monsterGroup
    exactGradedTrace : GVOA.ExactGradedTrace voaAction
    identityDimensionLaw :
      GVOA.IdentityTraceDimensionLaw voaAction exactGradedTrace

    exactCharacterTable : MCT.ExactMonsterCharacterTable
    firstCoefficientBridge : J.FirstMoonshineCoefficientBridge

    vNaturalConstruction : Set
    monsterIsFullVOAAutomorphismGroup : Set
    voaRationality : Set
    c2Cofiniteness : Set
    gradedCharacterModularity : Set
    mckayThompsonCoefficientLaw : Set
    genusZeroTheorem : Set

open MonsterGradedVOABridge public

monsterIdentityCoefficientIsGradeDimension :
  ∀ {Monster K} (bridge : MonsterGradedVOABridge Monster K) grade →
  GVOA.traceCoefficient (exactGradedTrace bridge)
    (GR.identity (GVOA.group (voaAction bridge))) grade
  ≡ GVOA.gradeDimensionAsScalar (identityDimensionLaw bridge) grade
monsterIdentityCoefficientIsGradeDimension bridge grade =
  GVOA.identityTraceCoefficientIsDimension
    (voaAction bridge)
    (exactGradedTrace bridge)
    (identityDimensionLaw bridge)
    grade

firstMoonshineArithmeticReused :
  196884 ≡ 1 + 196883
firstMoonshineArithmeticReused = J.firstCoefficientArithmetic

data MoonshineProofObligation : Set where
  coefficientNumerology : MoonshineProofObligation
  gradedRepresentationTrace : MoonshineProofObligation
  gradedVOAAxioms : MoonshineProofObligation
  monsterAutomorphismTheorem : MoonshineProofObligation
  modularityTheorem : MoonshineProofObligation
  genusZeroTheoremObligation : MoonshineProofObligation

coefficientNumerologyDoesNotConstructVOA :
  coefficientNumerology ≡ gradedVOAAxioms → ⊥
coefficientNumerologyDoesNotConstructVOA ()

modularityDoesNotCollapseToGenusZero :
  modularityTheorem ≡ genusZeroTheoremObligation → ⊥
modularityDoesNotCollapseToGenusZero ()

record VOAArithmeticGeometryCrossPollination : Set₁ where
  field
    gradedTraceToModularSeries : Set
    modularSeriesToArithmeticCoefficients : Set
    ellipticGenusOrCohomologyBridge : Set
    spectralOrLFunctionBridge : Set
    noAutomaticRiemannHypothesis : Set
    noAutomaticHodgeConjecture : Set
