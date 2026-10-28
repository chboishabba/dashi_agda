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
open import Agda.Builtin.List using (_∷_; [])
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
