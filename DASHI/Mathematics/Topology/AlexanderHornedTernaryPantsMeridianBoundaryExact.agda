module DASHI.Mathematics.Topology.AlexanderHornedTernaryPantsMeridianBoundaryExact where

------------------------------------------------------------------------
-- THREE-LEGGED PANTS -> 3D MERIDIAN: EXACT OBSTRUCTION AND CANDIDATE.
--
-- Reuse source owners:
-- * DASHI.Reasoning.RelationalBranchCobordismGeometry: canonical 1->3
--   COMBINATORIAL pants junction, not a smooth embedded surface.
-- * stacked #1254 TernaryCylinderPantsGeometryExact: slots/digits.
-- * #1244 AlexanderHornedBalancedTernaryCommutatorTowerExact:
--   actual proposed three-child free word [a,b][b,c].
--
-- The four-holed SPHERE has incoming peripheral word abc (up to
-- paths, orientation, conjugation). The proposed horn meridian
-- [a,b][b,c] has zero abelian image. These are NOT the same word.
--
-- A genus-two, one-boundary SURFACE has boundary [A,B][C,D].
-- Sending (A,B,C,D) to (a,b,b,c) gives [a,b][b,c].
-- This supplies an exact surface-group word map, but NOT an
-- injective map or an embedding of a surface or 3D handlebody.
-- The 3D relative collar / infinite wild linking remain open.
--
-- Classical surface group presentations, Hatcher AT Ex.2B.2,
-- and Alexander's 1924 binary wild sphere retain prior-art credit.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Data.Empty using (⊥)

import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Algebra.BalancedTernary as Trit
import DASHI.Reasoning.RelationalBranchCobordismGeometry as Pants
import DASHI.Mathematics.Topology.AlexanderHornedBalancedTernaryCommutatorTowerExact as Tower

-- This is only the original combinatorial junction theorem.
canonicalPantsHasThreeOutputs :
  Pants.outputCount Pants.composedOneToThree ≡ 3
canonicalPantsHasThreeOutputs = Pants.composedOutputCountIsThree

-- Finite character witnesses for NONIDENTITY of two free words.
evalC3 : (Tower.TernaryAddress → C3.C3) →
  Tower.TernaryWord → C3.C3
evalC3 f Tower.identityWord = C3.c0
evalC3 f (Tower.meridian w) = f w
evalC3 f (Tower.inverse w) = C3.inverse (evalC3 f w)
evalC3 f (Tower.multiply a b) =
  C3._∙_ (evalC3 f a) (evalC3 f b)

-- A group homomorphism from the free word presentation:
-- the first literal child maps to c1; zero/positive to c0.
firstChildCharacter : Tower.TernaryAddress → C3.C3
firstChildCharacter (Tower.ternary-address c (Trit.neg ∷ rest)) = C3.c1
firstChildCharacter _ = C3.c0

-- Peripheral boundary of genus-zero 1->3 pants surface.
pantsBoundaryWord : Tower.TernaryAddress → Tower.TernaryWord
pantsBoundaryWord w =
  Tower.multiply
    (Tower.meridian (Tower.child Trit.neg w))
    (Tower.multiply
      (Tower.meridian (Tower.child Trit.zero w))
      (Tower.meridian (Tower.child Trit.pos w)))

-- Actual three-child proposed horn bonding word lies in [F3,F3].
hornBoundaryWord : Tower.TernaryAddress → Tower.TernaryWord
hornBoundaryWord = Tower.refineMeridian

pantsBoundaryHasNonzeroCharacter : ∀ w →
  evalC3 firstChildCharacter (pantsBoundaryWord w) ≡ C3.c1
pantsBoundaryHasNonzeroCharacter w = refl

hornBoundaryHasZeroCharacter : ∀ w →
  evalC3 firstChildCharacter (hornBoundaryWord w) ≡ C3.c0
hornBoundaryHasZeroCharacter w = refl

pantsNotHornByAbelianCharacter : ∀ w →
  evalC3 firstChildCharacter (pantsBoundaryWord w)
    ≡ evalC3 firstChildCharacter (hornBoundaryWord w) → ⊥
pantsNotHornByAbelianCharacter w ()

-- A genus-two surface boundary is a PRODUCT OF TWO COMMUTATORS.
genusTwoBoundaryWord : Tower.TernaryWord → Tower.TernaryWord →
  Tower.TernaryWord → Tower.TernaryWord → Tower.TernaryWord
genusTwoBoundaryWord a b c d =
  Tower.multiply (Tower.commutator a b) (Tower.commutator c d)

-- The correct SURFACE-GROUP MAP target, with the shared b symbol.
ternaryHornAsGenusTwoSurfaceBoundary : ∀ w →
  hornBoundaryWord w ≡
    genusTwoBoundaryWord
      (Tower.meridian (Tower.child Trit.neg w))
      (Tower.meridian (Tower.child Trit.zero w))
      (Tower.meridian (Tower.child Trit.zero w))
      (Tower.meridian (Tower.child Trit.pos w))
ternaryHornAsGenusTwoSurfaceBoundary w = refl

-- No 3D embedding, π1-injectivity or same-object 3D handlebody
-- follows from this source-written surface-word coincidence.


-- STRONGER MINIMAL-GENUS REPAIR: cyclic conjugate of ONE commutator.
--
-- With [x,y]=x y x^-1 y^-1, the selected word
-- W = [a,b][b,c] = a b A c B C
-- is cyclically rotated into
--             B C a b A c = [B, C a].
-- Hence W is CONJUGATE to a single commutator, not merely the
-- boundary image of a genus-two surface. The representative source
-- is a once-punctured torus (genus 1, one boundary).
--
-- The cyclic rotation corresponds to moving the based peripheral
-- loop's basepoint along the boundary arc. No equality of based
-- words is claimed without the specified conjugating path.

singleCommutatorCyclicWord : Tower.TernaryAddress → Tower.TernaryWord
singleCommutatorCyclicWord w =
  Tower.commutator
    (Tower.inverse (Tower.meridian (Tower.child Trit.zero w)))
    (Tower.multiply
      (Tower.inverse (Tower.meridian (Tower.child Trit.pos w)))
      (Tower.meridian (Tower.child Trit.neg w)))

-- The RHS has free-reduced letters B C a b A c, which is precisely
-- the cyclic rotation by four letters of the original six-letter
-- free reduction a b A c B C. That is a free-group equality AFTER
-- cyclic conjugation, rather than syntax-level refl of TernaryWord.
--
-- A graph embedded as a theta ribbon spine has first Betti number
-- E-V+1 = 3-2+1 = 2, so it can be thickened to a genus-one,
-- one-boundary orientable ribbon surface with suitable cyclic edge
-- order. This abstract ribbon surface is NOT automatically the
-- original combinatorial 1->3 FOUR-boundary pants object.
--
-- No topological 3D embedding / meridian naturality is inferred.


------------------------------------------------------------------------
-- Exact LOCAL F3 free-reduction certificates.  This extends the
-- canonical pants/meridian owner instead of creating a duplicate owner.
--
-- Source: classic free-group/Nielsen operations; independent 2026-10-29
-- DASHI certificate for the already source-owned [a,b][b,c] word.
-- The root-sector C3 tower is NOT this local Nielsen C3.
--
-- These refl checks are concrete computations on freely reduced lists,
-- not a proof of correctness of the reducer for every word, nor
-- a geometric or kernel-verified cap-relative homeomorphism.
------------------------------------------------------------------------

module LocalNielsenReducedCertificate where
  open import Agda.Builtin.Bool using (Bool; true; false)

  data Letter : Set where
    posA negA posB negB posC negC : Letter

  Word : Set
  Word = List Letter

  infixr 5 _++w_
  _++w_ : Word → Word → Word
  [] ++w ys = ys
  (x ∷ xs) ++w ys = x ∷ (xs ++w ys)

  opposite : Letter → Letter
  opposite posA = negA
  opposite negA = posA
  opposite posB = negB
  opposite negB = posB
  opposite posC = negC
  opposite negC = posC

  cancel : Letter → Letter → Bool
  cancel posA negA = true
  cancel negA posA = true
  cancel posB negB = true
  cancel negB posB = true
  cancel posC negC = true
  cancel negC posC = true
  cancel _ _ = false

  push : Letter → Word → Word
  push x [] = x ∷ []
  push x (y ∷ ys) with cancel x y
  ... | true = ys
  ... | false = x ∷ y ∷ ys

  reduce : Word → Word
  reduce [] = []
  reduce (x ∷ xs) = push x (reduce xs)

  invert : Word → Word
  invert [] = []
  invert (x ∷ xs) = invert xs ++w (opposite x ∷ [])

  comm : Word → Word → Word
  comm x y = x ++w y ++w invert x ++w invert y

  a b c : Word
  a = posA ∷ []
  b = posB ∷ []
  c = posC ∷ []

  -- Evaluate the ORIGINAL canonical three-child syntax at one
  -- selected ternary root.  Only the newest child trit is read.
  -- This is not a faithful evaluation of arbitrary tower addresses.
  childLetter : Tower.TernaryAddress → Word
  childLetter (Tower.ternary-address _ (Trit.neg ∷ _)) = a
  childLetter (Tower.ternary-address _ (Trit.zero ∷ _)) = b
  childLetter (Tower.ternary-address _ (Trit.pos ∷ _)) = c
  childLetter _ = []

  evalTower : Tower.TernaryWord → Word
  evalTower Tower.identityWord = []
  evalTower (Tower.meridian x) = childLetter x
  evalTower (Tower.inverse x) = invert (evalTower x)
  evalTower (Tower.multiply x y) = evalTower x ++w evalTower y

  canonicalRoot : Tower.TernaryAddress
  canonicalRoot = Tower.ternary-address C3.c0 []

  w : Word
  w = evalTower (hornBoundaryWord canonicalRoot)

  canonicalWordReduction :
    reduce w ≡
      (posA ∷ posB ∷ negA ∷ posC ∷ negB ∷ negC ∷ [])
  canonicalWordReduction = refl

  -- u=B, v=C a, z=c is the source-owned Nielsen basis.
  u v z p : Word
  u = invert b
  v = invert c ++w a
  z = c
  p = a ++w b ++w invert a ++w c

  puncturedTorusBoundary :
    reduce (invert p ++w w ++w p) ≡ reduce (comm u v)
  puncturedTorusBoundary = refl

  -- The nonlinear 3-cycle in the original (a,b,c) coordinates.
  -- a -> c A c b, b -> A c, c -> c.
  image : Letter → Word
  image posA = posC ∷ negA ∷ posC ∷ posB ∷ []
  image posB = negA ∷ posC ∷ []
  image posC = c
  image negA = negB ∷ negC ∷ posA ∷ negC ∷ []
  image negB = negC ∷ posA ∷ []
  image negC = negC ∷ []

  substitute : Word → Word
  substitute [] = []
  substitute (x ∷ xs) = image x ++w substitute xs

  phi : Word → Word
  phi xs = reduce (substitute xs)

  phiOnU : phi u ≡ reduce v
  phiOnU = refl

  phiOnV : phi v ≡ reduce (invert v ++w invert u)
  phiOnV = refl

  phiOnZ : phi z ≡ z
  phiOnZ = refl

  phiCubedOnA : phi (phi (phi a)) ≡ a
  phiCubedOnA = refl

  phiCubedOnB : phi (phi (phi b)) ≡ b
  phiCubedOnB = refl

  phiCubedOnC : phi (phi (phi c)) ≡ c
  phiCubedOnC = refl

  phiNonidentityOnA : phi a ≡ a → ⊥
  phiNonidentityOnA ()

  -- Explicit based conjugator q=c A c A: not just a cyclic
  -- word-equality oracle or an unrelated S3 fingerprint.
  q : Word
  q = c ++w invert a ++w c ++w invert a

  phiPreservesPeripheralConjugacy :
    phi w ≡ reduce (q ++w w ++w invert q)
  phiPreservesPeripheralConjugacy = refl

  -- Without a based-path conjugacy correction, local Nielsen C3
  -- fails STRICT meridian naturality: phi(w) is not literally w.
  -- This is a genuine extra acceptance condition for G4.
  phiNotStrictlyBasedPeripheral : phi w ≡ reduce w → ⊥
  phiNotStrictlyBasedPeripheral ()

  nontrivialParentMeridian : reduce w ≡ [] → ⊥
  nontrivialParentMeridian ()

-- The three-generator check, together with the free-group universal
-- property, identifies the mathematical order-three automorphism.
-- An unrestricted arbitrary-word Agda theorem (and exact-head Agda
-- kernel receipt) is not claimed here.  No local finite-order 3D
-- homeomorphism or G2–G6 geometry is constructed by these computations.


------------------------------------------------------------------------
-- MOD-THREE MODULE OBSTRUCTION, NOT MERELY A SIGNED-LABEL NO-GO.
--
-- On abelianization, the local peripheral-preserving Nielsen map has
-- matrix columns (-1,1,2), (-1,0,1), (0,0,1) over Z; a literal
-- cyclic permutation has columns (0,1,0),(0,0,1),(1,0,0).
-- In F3^3 the Nielsen map has NINE fixed points, whereas cyclic
-- permutation has THREE.  A conjugating GL3(Z) matrix would induce
-- a bijection modulo three preserving fixed-point cardinality;
-- hence no such basis conjugacy exists.  This is independent of
-- their matching characteristic polynomial (t-1)(t²+t+1).
--
-- Exact 27-case Agda calculations below REUSE the existing C3
-- groupElements and group law.  The final GL3/F3 conjugacy argument
-- is mathematical reasoning outside this finite computational scope.
-- No 3D periodic homeomorphism or physical 27-cell identification.
------------------------------------------------------------------------

module NielsenMod3PermutationBarrier where
  open import Agda.Builtin.Bool using (Bool; true; false)

  data Vec3 : Set where
    triple : C3.C3 → C3.C3 → C3.C3 → Vec3

  infixr 5 _++list_
  _++list_ : ∀ {A : Set} → List A → List A → List A
  [] ++list ys = ys
  (x ∷ xs) ++list ys = x ∷ (xs ++list ys)

  mapList : ∀ {A B : Set} → (A → B) → List A → List B
  mapList f [] = []
  mapList f (x ∷ xs) = f x ∷ mapList f xs

  bindList : ∀ {A B : Set} → (A → List B) → List A → List B
  bindList f [] = []
  bindList f (x ∷ xs) = f x ++list bindList f xs

  allAbelianTriples : List Vec3
  allAbelianTriples =
    bindList (λ x →
      bindList (λ y →
        mapList (λ z → triple x y z) C3.groupElements)
      C3.groupElements)
    C3.groupElements

  eqC3 : C3.C3 → C3.C3 → Bool
  eqC3 C3.c0 C3.c0 = true
  eqC3 C3.c1 C3.c1 = true
  eqC3 C3.c2 C3.c2 = true
  eqC3 _ _ = false

  eqVec : Vec3 → Vec3 → Bool
  eqVec (triple a b c) (triple x y z)
    with eqC3 a x | eqC3 b y | eqC3 c z
  ... | true | true | true = true
  ... | _ | _ | _ = false

  permutation3 : Vec3 → Vec3
  permutation3 (triple a b c) = triple c a b

  -- Matrix of the actual source-owned phi on abelianized (a,b,c):
  --  a -> c A c b, b -> A c, c -> c.
  nielsen3 : Vec3 → Vec3
  nielsen3 (triple a b c) =
    triple
      (C3._∙_ (C3.inverse a) (C3.inverse b))
      a
      (C3._∙_ (C3._∙_ (C3._∙_ a a) b) c)

  fixed : (Vec3 → Vec3) → List Vec3 → List Vec3
  fixed f [] = []
  fixed f (v ∷ vs) with eqVec (f v) v
  ... | true = v ∷ fixed f vs
  ... | false = fixed f vs

  allAbelianTriplesCount : C3.length allAbelianTriples ≡ 27
  allAbelianTriplesCount = refl

  literalCycleFixedCount :
    C3.length (fixed permutation3 allAbelianTriples) ≡ 3
  literalCycleFixedCount = refl

  localNielsenFixedCount :
    C3.length (fixed nielsen3 allAbelianTriples) ≡ 9
  localNielsenFixedCount = refl

  unequalMod3FixedCounts :
    C3.length (fixed permutation3 allAbelianTriples)
      ≡ C3.length (fixed nielsen3 allAbelianTriples) → ⊥
  unequalMod3FixedCounts ()

-- This supplies a concrete obstruction to changing a literal child
-- three-cycle INTO the nonlinear Nielsen peripheral stabilizer by
-- conjugation in Aut(F3) (even after allowing GL3(Z) on H1).
-- It does not forbid other geometric realizations of either action.
