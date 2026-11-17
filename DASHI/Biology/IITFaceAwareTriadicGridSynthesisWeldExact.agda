module DASHI.Biology.IITFaceAwareTriadicGridSynthesisWeldExact where

------------------------------------------------------------------------
-- MATCHED HIGHER-ORDER EXPERIMENT = BINARY SYNTHESIS FABRIC + ABC CONTROL
--
-- The existing face-aware TPM pair is already the clean experiment comparing
-- higher-order organization from ordinary binary synthesis against one genuine
-- primitive three-way interaction.  This module makes that interpretation exact
-- instead of constructing a redundant second fixture.
--
-- Pairwise model:
--
--   (B,C) -> A' by XOR
--   (A,C) -> B' by XOR
--   (A,B) -> C' by XOR
--
-- Thus every output is an ordinary two-input/one-output synthesis cell on the
-- same generic fabric used by the XOR-grid owner.  The matched triadic model
-- changes only C' by XORing the pure interior term A*B*C.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.IITFaceAwareTriadicCausalPairExact as Face
import DASHI.Biology.IITXORGridSynthesisFabricExact as Grid

------------------------------------------------------------------------
-- 1. Three-site synthesis fabric.
------------------------------------------------------------------------

data TriSite : Set where
  siteA siteB siteC : TriSite

triangleFabric : Grid.TwoInputFabric TriSite
triangleFabric = Grid.two-input-fabric sourceA sourceB
  where
    sourceA : TriSite → TriSite
    sourceA siteA = siteB
    sourceA siteB = siteA
    sourceA siteC = siteA

    sourceB : TriSite → TriSite
    sourceB siteA = siteC
    sourceB siteB = siteC
    sourceB siteC = siteB

-- A and B already form a literal two-edge recurrent dependency cycle.
triangleHasABRecurrence :
  Grid.inputASource triangleFabric siteA ≡ siteB
  × Grid.inputASource triangleFabric siteB ≡ siteA
triangleHasABRecurrence = refl , refl

tripleField : Face.BitTriple → Grid.BoolField TriSite
tripleField state siteA = Face.bitA state
tripleField state siteB = Face.bitB state
tripleField state siteC = Face.bitC state

pairwiseOutputField : Face.BitTriple → Grid.BoolField TriSite
pairwiseOutputField state = tripleField (Face.pairwiseStep state)

pairwiseIsExactlyThreeBinarySynthesisCells :
  (state : Face.BitTriple) →
  (site : TriSite) →
  pairwiseOutputField state site
  ≡ Grid.xorFabricStep triangleFabric (tripleField state) site
pairwiseIsExactlyThreeBinarySynthesisCells state siteA = refl
pairwiseIsExactlyThreeBinarySynthesisCells state siteB = refl
pairwiseIsExactlyThreeBinarySynthesisCells state siteC = refl

------------------------------------------------------------------------
-- 2. The matched model adds one and only one primitive ABC interaction at C'.
------------------------------------------------------------------------

triadicInteriorTerm : Face.BitTriple → TriSite → Bool
triadicInteriorTerm state siteA = false
triadicInteriorTerm state siteB = false
triadicInteriorTerm state siteC =
  Face.and3 (Face.bitA state) (Face.bitB state) (Face.bitC state)

triadicFabricStep : Face.BitTriple → Grid.BoolField TriSite
triadicFabricStep state site =
  Face.xorB
    (Grid.xorFabricStep triangleFabric (tripleField state) site)
    (triadicInteriorTerm state site)

triadicOutputField : Face.BitTriple → Grid.BoolField TriSite
triadicOutputField state = tripleField (Face.triadicStep state)

triadicIsPairwiseFabricPlusABC :
  (state : Face.BitTriple) →
  (site : TriSite) →
  triadicOutputField state site ≡ triadicFabricStep state site
triadicIsPairwiseFabricPlusABC state siteA = refl
triadicIsPairwiseFabricPlusABC state siteB = refl
triadicIsPairwiseFabricPlusABC state siteC = refl

------------------------------------------------------------------------
-- 3. The primitive higher-order correction vanishes on every coordinate face.
------------------------------------------------------------------------

abcVanishesOnAZero :
  (b c : Bool) →
  triadicInteriorTerm (Face.bits false b c) siteC ≡ false
abcVanishesOnAZero b c = refl

abcVanishesOnBZero :
  (a c : Bool) →
  triadicInteriorTerm (Face.bits a false c) siteC ≡ false
abcVanishesOnBZero false c = refl
abcVanishesOnBZero true c = refl

abcVanishesOnCZero :
  (a b : Bool) →
  triadicInteriorTerm (Face.bits a b false) siteC ≡ false
abcVanishesOnCZero false b = refl
abcVanishesOnCZero true false = refl
abcVanishesOnCZero true true = refl

abcNonzeroAtInterior :
  triadicInteriorTerm Face.ones siteC ≡ true
abcNonzeroAtInterior = refl

------------------------------------------------------------------------
-- 4. Scientific boundary.
------------------------------------------------------------------------

record EmergentVsPrimitiveHigherOrderBoundary : Set where
  constructor emergent-vs-primitive-higher-order-boundary
  field
    pairwiseModelUsesOnlyBinarySynthesisCells : Bool
    pairwiseModelHasExplicitRecurrentDependencyCycle : Bool
    matchedTriadicModelUsesSameBinaryFabric : Bool
    matchedTriadicModelAddsPureABCInteriorTerm : Bool
    pureABCTermVanishesOnCoordinateFaces : Bool
    primitiveThreeInputGateRequiredForAllHigherOrderIntegration : Bool
    scalarSystemPhiCompletelyClassifiesHigherOrderStructure : Bool
open EmergentVsPrimitiveHigherOrderBoundary public

canonicalEmergentVsPrimitiveHigherOrderBoundary :
  EmergentVsPrimitiveHigherOrderBoundary
canonicalEmergentVsPrimitiveHigherOrderBoundary =
  emergent-vs-primitive-higher-order-boundary
    true true true true true false false
