module DASHI.Moonshine.Monster27VOAOnsiteCube369BridgeExact where

-- ACTUAL provenance owners:
-- FLM V^natural, real Monster automorphism group, weight-2 Griess
-- and irreducible 196883 action: pre-existing DASHI WeightTwoLinearActionBridge.
-- Pre-existing Selected3BSameElementSource carries literal VOA endomorphism
-- and same-object grade-two trace for a selected Monster 3B element.
-- Literature: Monster classes 27A/27B have g^9 in 3B;
-- T_3B=q^-1+54q-76q^2+... (Conway-Norton, FLM/Borcherds).
-- New: an ORDER27 generator is tied to SAME selected3B element by an
-- EXPLICIT g^9 equality, not by cardinality, name or generic trit.
-- Source record has no fabricated inhabitant: genuine Monster action
-- and g^9 receipt must be provided.
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Empty using (⊥)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Moonshine.JInvariant369Cube27ModularSliceActionExact as Slice
import DASHI.Geometry.HilbertLorentzForcing as Linear
import DASHI.Moonshine.GradedRepresentation as GR
import DASHI.Moonshine.GradedVertexOperatorAlgebraBoundary as GVOA
import DASHI.Moonshine.MonsterGradedVOABridgeExact as Legacy
import DASHI.Moonshine.MonsterGradedVOALiteralActionSameObjectBidiExact as Weld
import DASHI.Moonshine.MonsterGradedVOASelected3BSameElementBidiExact as Selected
import DASHI.Moonshine.MonsterWeightTwoLinearActionBridgeExact as WeightTwo
import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as ThreeB

ownerGroup :
  ∀ {Monster K : Set} →
  Selected.Selected3BSameElementSource Monster K → GR.Group Monster
ownerGroup s =
  GVOA.group (Legacy.voaAction (Weld.gradedAuthority (Selected.weld s)))

power :
  ∀ {Monster K : Set} →
  (source : Selected.Selected3BSameElementSource Monster K) →
  Nat → Monster → Monster
power source zero g = GR.Group.identity (ownerGroup source)
power source (suc n) g =
  GR.Group._∙_ (ownerGroup source) g (power source n g)

record Monster27VOAOnCubeSource (Monster K : Set) : Setω where
  field
    selected3B : Selected.Selected3BSameElementSource Monster K

    weightTwoLinear :
      WeightTwo.WeightTwoLinearActionBridge
        (Weld.gradedAuthority (Selected.weld selected3B))

    g27 : Monster

    twentySevenOrderReceipt :
      power selected3B 27 g27 ≡ GR.Group.identity (ownerGroup selected3B)

    ninthPowerIsSelected3B :
      power selected3B 9 g27 ≡
      Selected.selectedCentralElement selected3B

    -- The actual grade-two scalar is an existing K-valued trace.
    -- Mapping this K into a published integer requires explicit
    -- source/calibration data, not a mere statement that its name is 3B.
    sourceTraceToNat : K → Nat
    certified3BGradeTwoTrace :
      sourceTraceToNat (Selected.selectedCentralGradeTwoTrace selected3B)
      ≡ 54

open Monster27VOAOnCubeSource public

-- The 196883 linear Monster representation is the REAL source-owned
-- weight-two constituent. Each physical site would carry that SAME
-- representation, rather than 27 ad-hoc local states.
Constituent : ∀ {Monster K : Set} →
  Monster27VOAOnCubeSource Monster K → Set
Constituent source =
  Linear.Vector (WeightTwo.constituentLinearCarrier (weightTwoLinear source))

CubeWave : ∀ {Monster K : Set} →
  Monster27VOAOnCubeSource Monster K → Set
CubeWave source = Cube.Ternary27Point → Constituent source

onsite : ∀ {Monster K : Set}
  (source : Monster27VOAOnCubeSource Monster K) →
  Monster → CubeWave source → CubeWave source
onsite source g wave position =
  WeightTwo.constituentAct (weightTwoLinear source) g (wave position)

relabel : ∀ {Monster K : Set}
  (source : Monster27VOAOnCubeSource Monster K) →
  (Cube.Ternary27Point → Cube.Ternary27Point) →
  CubeWave source → CubeWave source
relabel source transform wave position = wave (transform position)

-- Exact operator commutation on the same V^natural grade-two linear
-- constituent at ALL 27 *actual spatial* cube sites, irrespective
-- of whether the site permutation preserves the cube Hamiltonian.
onsiteCommutesWithSpatialRelabelling :
  ∀ {Monster K : Set}
  (source : Monster27VOAOnCubeSource Monster K) →
  (g : Monster) →
  (transform : Cube.Ternary27Point → Cube.Ternary27Point) →
  (wave : CubeWave source) →
  onsite source g (relabel source transform wave)
  ≡ relabel source transform (onsite source g wave)
onsiteCommutesWithSpatialRelabelling source g transform wave = refl

onsiteCommutesWithSelectedModularPermutation :
  ∀ {Monster K : Set}
  (source : Monster27VOAOnCubeSource Monster K) →
  (wave : CubeWave source) →
  onsite source (g27 source)
    (relabel source Slice.modularSheetAction wave)
  ≡ relabel source Slice.modularSheetAction
      (onsite source (g27 source) wave)
onsiteCommutesWithSelectedModularPermutation source wave = refl

-- The source's actual order27 parent ninth power is the SAME
-- Monster 3B literal VOA/trace element, by a typed producer equality.
ninthChargeIsActual3BOnCube :
  ∀ {Monster K : Set}
  (source : Monster27VOAOnCubeSource Monster K) →
  (wave : CubeWave source) →
  onsite source (power (selected3B source) 9 (g27 source)) wave
  ≡ onsite source (Selected.selectedCentralElement (selected3B source)) wave
ninthChargeIsActual3BOnCube source wave
  rewrite ninthPowerIsSelected3B source = refl

-- Exact sourced numerical charge split, NOT a newly constructed
-- diagonalisation of the 196883x196883 Monster matrices.
weightTwoDimension : Nat
weightTwoDimension = 196884

threeBTrace : Nat
threeBTrace = 54

neutralCount : Nat
neutralCount = 65664

positiveCount : Nat
positiveCount = 65610

negativeCount : Nat
negativeCount = 65610

primitivePerRoot : Nat
primitivePerRoot = 7290

threeBCharacterEquation :
  3 * positiveCount + threeBTrace ≡ weightTwoDimension
threeBCharacterEquation = refl

threeBCharacterSplit :
  neutralCount + positiveCount + negativeCount ≡ weightTwoDimension
threeBCharacterSplit = refl

primitive27AllRoots :
  18 * primitivePerRoot ≡ 131220
primitive27AllRoots = refl

eachSignedChargeHasNinePrimitiveRoots :
  9 * primitivePerRoot ≡ positiveCount
eachSignedChargeHasNinePrimitiveRoots = refl

-- Pre-existing F3^6 x Fin90 model accounts for each 3B nontrivial
-- eigenspace. A primitive refinement is 9 x (81 x 90), as dimensions.
-- A *basis-intertwining* identification on the actual Monster
-- representation is still an independent physical/math producer.
prior3BModelMatchesSignedCount : 729 * 90 ≡ positiveCount
prior3BModelMatchesSignedCount = refl

primitiveMultiplicityMatchesSubfibre : 81 * 90 ≡ primitivePerRoot
primitiveMultiplicityMatchesSubfibre = refl

-- The 27 cube is the spatial carrier, not the cyclic group of g27.
-- Commutation with coordinate relabelling is NOT invariance of the
-- cube nearest-neighbour Hamiltonian under that relabelling.
-- TwistedMonster VOA module, boundary multiplier and bulk KK/AdS3
-- remain with their original TwistedModuleModularity owners.
