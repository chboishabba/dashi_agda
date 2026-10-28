module DASHI.Mathematics.Topology.AlexanderHornedDepthTwoFiveOrbitFibreExact where

------------------------------------------------------------------------
-- EXACT 27 -> 9 -> 5 -> 3^5 symmetry-reduced native fibre action.
--
-- Existing owners: native C3 x Trit^N end tower, finite C3 group,
-- native ternary fibre action, 13/27 and 5/9 source PR #1407,
-- independent 3^5 vs 5^3 source PR #1414.
--
-- The H=C3_sector x C2_sign-invariant phase fields on the depth-two
-- 27 addresses are in pointwise bijection with the fields on FIVE
-- explicit orbit representatives of simultaneous sign reversal.
-- This is a genuine orbit-invariant field correspondence, NOT a
-- direct identification of the 27 addresses with a 5-element set.
-- Its optional sixth trit is an INDEPENDENT field coordinate.
--
-- Alexander/Hatcher's original wild source is NOT proved here.
-- Riemann/RH, Pickover real-angle phase and Ibrahim Monster 3B
-- retain independent owners. Source-written Agda, kernel pending.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Data.Vec.Base using (_∷_; [])

import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Algebra.BalancedTernary as T
import DASHI.Mathematics.Topology.AlexanderHornedNativeBalancedTernaryEndTowerExact as End
import DASHI.Mathematics.Topology.AlexanderHornedNativeTernaryFibreActionExact as Fibre

data FiveOrbit : Set where
  origin axisFirst axisSecond diagonal antiDiagonal : FiveOrbit

-- Classification is deterministic without quotient axioms or
-- propositional function-extensionality.
orbit : T.Trit → T.Trit → FiveOrbit
orbit T.zero T.zero = origin
orbit T.neg  T.zero = axisFirst
orbit T.pos  T.zero = axisFirst
orbit T.zero T.neg  = axisSecond
orbit T.zero T.pos  = axisSecond
orbit T.neg  T.neg  = diagonal
orbit T.pos  T.pos  = diagonal
orbit T.neg  T.pos  = antiDiagonal
orbit T.pos  T.neg  = antiDiagonal

orbitReflect : ∀ a b →
  orbit (T.negate a) (T.negate b) ≡ orbit a b
orbitReflect T.neg T.neg = refl
orbitReflect T.neg T.zero = refl
orbitReflect T.neg T.pos = refl
orbitReflect T.zero T.neg = refl
orbitReflect T.zero T.zero = refl
orbitReflect T.zero T.pos = refl
orbitReflect T.pos T.neg = refl
orbitReflect T.pos T.zero = refl
orbitReflect T.pos T.pos = refl

representative : FiveOrbit → T.Trit × T.Trit
representative origin = T.zero , T.zero
representative axisFirst = T.neg , T.zero
representative axisSecond = T.zero , T.neg
representative diagonal = T.neg , T.neg
representative antiDiagonal = T.neg , T.pos

-- The FULL 27-site local phase field already has a group structure.
DepthTwoField : Set
DepthTwoField = Fibre.PhaseField 2

-- Fixed under external sector C3 and simultaneous sign reversal.
record Invariant27 (f : DepthTwoField) : Set where
  field
    sectorFixed : ∀ c a b →
      f (c , (a ∷ b ∷ [])) ≡
      f (C3.c0 , (a ∷ b ∷ []))
    signFixed : ∀ a b →
      f (C3.c0 , (T.negate a ∷ T.negate b ∷ [])) ≡
      f (C3.c0 , (a ∷ b ∷ []))

FiveField : Set
FiveField = FiveOrbit → C3.C3

-- Every five-field supplies a field invariant under BOTH symmetries.
inflate : FiveField → DepthTwoField
inflate k (c , (a ∷ b ∷ [])) = k (orbit a b)

inflateInvariant : ∀ k → Invariant27 (inflate k)
inflateInvariant k = record
  { sectorFixed = λ c a b → refl
  ; signFixed = λ a b → cong k (orbitReflect a b)
  }

deflate : DepthTwoField → FiveField
deflate f o with representative o
... | (a , b) = f (C3.c0 , (a ∷ b ∷ []))

deflateInflate : ∀ k o → deflate (inflate k) o ≡ k o
deflateInflate k origin = refl
deflateInflate k axisFirst = refl
deflateInflate k axisSecond = refl
deflateInflate k diagonal = refl
deflateInflate k antiDiagonal = refl

-- For a GENERAL sector/sign invariant field, these are the 9
-- pointwise orbit normal forms. Each proof is a single application
-- of the invariant condition or definitionally identical.
fieldOrbitNormalForm : ∀ f →
  Invariant27 f → ∀ a b →
  f (C3.c0 , (a ∷ b ∷ [])) ≡ deflate f (orbit a b)
fieldOrbitNormalForm f invariant T.neg T.neg = refl
fieldOrbitNormalForm f invariant T.neg T.zero = refl
fieldOrbitNormalForm f invariant T.neg T.pos = refl
fieldOrbitNormalForm f invariant T.zero T.neg = refl
fieldOrbitNormalForm f invariant T.zero T.zero = refl
fieldOrbitNormalForm f invariant T.zero T.pos =
  sym (Invariant27.signFixed invariant T.zero T.pos)
fieldOrbitNormalForm f invariant T.pos T.neg =
  sym (Invariant27.signFixed invariant T.pos T.neg)
fieldOrbitNormalForm f invariant T.pos T.zero =
  sym (Invariant27.signFixed invariant T.pos T.zero)
fieldOrbitNormalForm f invariant T.pos T.pos =
  sym (Invariant27.signFixed invariant T.pos T.pos)

inflateDeflateInvariant : ∀ f →
  (inv : Invariant27 f) → ∀ c a b →
  inflate (deflate f) (c , (a ∷ b ∷ [])) ≡
    f (c , (a ∷ b ∷ []))
inflateDeflateInvariant f inv c a b =
  trans (sym (fieldOrbitNormalForm f inv a b))
        (sym (Invariant27.sectorFixed inv c a b))

-- Componentwise C3 addition commutes with the reduction.
inflateCombines : ∀ k l c a b →
  inflate (λ o → C3._∙_ (k o) (l o)) (c , (a ∷ b ∷ []))
  ≡ C3._∙_ (inflate k (c , (a ∷ b ∷ [])))
             (inflate l (c , (a ∷ b ∷ [])))
inflateCombines k l c a b = refl

-- A SEPARATE external phase coordinate yields 3^6=729 states.
-- If it duplicates one of the existing five orbit values, it is not
-- independent and its cardinality cannot be multiplied by three.
SixPhaseState : Set
SixPhaseState = FiveField × C3.C3


------------------------------------------------------------------------
-- NEW NATURAL 3^5 vs 5^3 TRANSPORT: REVERSE DOMAIN AND CODOMAIN.
--
--   FiveField = (FiveOrbit -> C3)        -- 3^5 = 243, group
--   ThreeOrbitSelection = (C3 -> FiveOrbit)  -- 5^3 = 125, set
--
-- Neither requires an invented C5 GROUP operation on FiveOrbit.
-- Their canonical relation is composition/evaluation, not a bijection:
-- field . selection : C3 -> C3.
-- Choose three distinct orbits and every three-phase readout lifts
-- to a FiveField; the other TWO orbit values remain unobservable.
--
-- This is an exact SOURCE-SPECIFIC BIDI / fibre information-loss result,
-- not a numerical 243↔125 coincidence, and it preserves the original
-- invariant27 / 13-in-27 / 5-in-9 owners above.
------------------------------------------------------------------------

ThreeOrbitSelection : Set
ThreeOrbitSelection = C3.C3 → FiveOrbit

ThreeSectorPhaseReadout : Set
ThreeSectorPhaseReadout = C3.C3 → C3.C3

evaluateAlongSelection :
  FiveField → ThreeOrbitSelection → ThreeSectorPhaseReadout
evaluateAlongSelection phase selector sector =
  phase (selector sector)

-- The recipient is a first-class, complete three-sector finite
-- observation table; this avoids assuming function extensionality.
ThreePhaseCode : Set
ThreePhaseCode = C3.C3 × (C3.C3 × C3.C3)

readoutCode :
  FiveField → ThreeOrbitSelection → ThreePhaseCode
readoutCode phase selector =
  phase (selector C3.c0) ,
    (phase (selector C3.c1) , phase (selector C3.c2))

selectionOfThreeOrbits : ThreeOrbitSelection
selectionOfThreeOrbits C3.c0 = origin
selectionOfThreeOrbits C3.c1 = axisFirst
selectionOfThreeOrbits C3.c2 = axisSecond

liftThreePhaseCode : ThreePhaseCode → FiveField
liftThreePhaseCode (a , (b , c)) origin = a
liftThreePhaseCode (a , (b , c)) axisFirst = b
liftThreePhaseCode (a , (b , c)) axisSecond = c
liftThreePhaseCode (a , (b , c)) diagonal = C3.c0
liftThreePhaseCode (a , (b , c)) antiDiagonal = C3.c0

readoutCodeHasSection :
  (code : ThreePhaseCode) →
  readoutCode (liftThreePhaseCode code) selectionOfThreeOrbits ≡ code
readoutCodeHasSection (a , (b , c)) = refl

-- Pointwise group structure on the five orbit-phase fields and
-- its compatibility with evaluation; the 5-orbit selection is
-- deliberately only a SET without artificial 5-element group law.
fiveFieldAdd : FiveField → FiveField → FiveField
fiveFieldAdd f g o = C3._∙_ (f o) (g o)

readoutPreservesGroupOperation :
  (f g : FiveField) (selector : ThreeOrbitSelection)
  (sector : C3.C3) →
  evaluateAlongSelection (fiveFieldAdd f g) selector sector
  ≡ C3._∙_ (evaluateAlongSelection f selector sector)
            (evaluateAlongSelection g selector sector)
readoutPreservesGroupOperation f g selector sector = refl

-- Two distinct fields with IDENTICAL three-sector readouts.
allNeutralFiveField : FiveField
allNeutralFiveField _ = C3.c0

diagonalOnlyCharge : FiveField
diagonalOnlyCharge origin = C3.c0
diagonalOnlyCharge axisFirst = C3.c0
diagonalOnlyCharge axisSecond = C3.c0
diagonalOnlyCharge diagonal = C3.c1
diagonalOnlyCharge antiDiagonal = C3.c0

sameThreeSectorReadout :
  readoutCode allNeutralFiveField selectionOfThreeOrbits
  ≡ readoutCode diagonalOnlyCharge selectionOfThreeOrbits
sameThreeSectorReadout = refl

invisibleDiagonalDiffers :
  allNeutralFiveField diagonal ≡ diagonalOnlyCharge diagonal → ⊥
invisibleDiagonalDiffers ()

noUniversalFiveFieldRecoveryFromThreeSelectedOrbits :
  (recover : ThreePhaseCode → FiveField) →
  ((f : FiveField) (o : FiveOrbit) →
     recover (readoutCode f selectionOfThreeOrbits) o ≡ f o)
  → ⊥
noUniversalFiveFieldRecoveryFromThreeSelectedOrbits recover exact =
  invisibleDiagonalDiffers
    (trans
      (sym (exact allNeutralFiveField diagonal))
      (trans
        (cong (λ code → recover code diagonal)
          sameThreeSectorReadout)
        (exact diagonalOnlyCharge diagonal)))

-- The five phase slots contain two unobserved independent components
-- under this chosen three-sector selector. Their kernel is C3^2
-- (nine fields). That count is an independent finite group calculation;
-- the code above establishes a *stronger concrete non-descent witness*.


------------------------------------------------------------------------
-- COMPLETE KERNEL NORMAL FORM for the selected three-orbit evaluation.
-- Kernel = exactly two independent C3 coordinates, i.e. C3 × C3.
-- This goes beyond a collision fixture; it is a TWO-SIDED finite
-- parametrisation of ALL five-orbit fields with neutral readout.
------------------------------------------------------------------------

FreeInvisiblePair : Set
FreeInvisiblePair = C3.C3 × C3.C3

freeInvisibleField : FreeInvisiblePair → FiveField
freeInvisibleField (a , b) origin = C3.c0
freeInvisibleField (a , b) axisFirst = C3.c0
freeInvisibleField (a , b) axisSecond = C3.c0
freeInvisibleField (a , b) diagonal = a
freeInvisibleField (a , b) antiDiagonal = b

invisibleCoordinates : FiveField → FreeInvisiblePair
invisibleCoordinates f = f diagonal , f antiDiagonal

freeInvisiblePairRoundTrip :
  (pair : FreeInvisiblePair) →
  invisibleCoordinates (freeInvisibleField pair) ≡ pair
freeInvisiblePairRoundTrip (a , b) = refl

record NeutralThreeReadout (f : FiveField) : Set where
  field
    originNeutral : f origin ≡ C3.c0
    axisFirstNeutral : f axisFirst ≡ C3.c0
    axisSecondNeutral : f axisSecond ≡ C3.c0

open NeutralThreeReadout public

freeFieldHasNeutralReadout :
  (pair : FreeInvisiblePair) →
  NeutralThreeReadout (freeInvisibleField pair)
freeFieldHasNeutralReadout pair = record
  { originNeutral = refl
  ; axisFirstNeutral = refl
  ; axisSecondNeutral = refl
  }

allNeutralReadoutFieldsFromTwoCoordinates :
  (f : FiveField) →
  (neutral : NeutralThreeReadout f) →
  (o : FiveOrbit) →
  freeInvisibleField (invisibleCoordinates f) o ≡ f o
allNeutralReadoutFieldsFromTwoCoordinates f neutral origin =
  sym (originNeutral neutral)
allNeutralReadoutFieldsFromTwoCoordinates f neutral axisFirst =
  sym (axisFirstNeutral neutral)
allNeutralReadoutFieldsFromTwoCoordinates f neutral axisSecond =
  sym (axisSecondNeutral neutral)
allNeutralReadoutFieldsFromTwoCoordinates f neutral diagonal = refl
allNeutralReadoutFieldsFromTwoCoordinates f neutral antiDiagonal = refl

freeFieldReadoutNeutral :
  (pair : FreeInvisiblePair) →
  readoutCode (freeInvisibleField pair) selectionOfThreeOrbits
  ≡ C3.c0 , (C3.c0 , C3.c0)
freeFieldReadoutNeutral pair = refl

-- Source theorem: kernel of the readout morphism is pointwise
-- isomorphic to C3². The order 9 follows from known C3 cardinality.
-- This kernel does not equal an SU2 central kernel or a Monster orbit.
