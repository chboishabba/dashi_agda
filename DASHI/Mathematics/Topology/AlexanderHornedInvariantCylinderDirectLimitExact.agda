module DASHI.Mathematics.Topology.AlexanderHornedInvariantCylinderDirectLimitExact where

------------------------------------------------------------------------
-- Algebraic direct-limit SETOID for sector+sign-invariant cylinder fields.
--
-- Reuses ORIGINAL #1244 owners: NativeBalancedTernaryEndTowerExact,
-- NativeTernaryFibreActionExact.SectorSignInvariant, pullback, evalLocal.
-- No second gauge carrier, no quotient postulate or function extensionality.
--
-- Main new results:
--   1. Construct any two fields' common finite refinement.
--   2. Prove group laws on invariant finite-cylinder representatives
--      UP TO pointwise equality on the inverse-limit end space.
--   3. Construct an end extending EVERY finite prefix (zero tail).
--   4. Equate common-refinement equality with equality on ALL ends.
--
-- Classical roots: filtered colimits and profinite inverse limits;
-- see Stacks Project Tag 08ZW (profinite spaces). Source extension:
-- Johl Brown-directed / OpenAI ChatGPT-assisted, 2026-10-28.
-- This does not establish the compactness/continuous-factorisation
-- converse, an ambient wild embedding, an RH/Monster/Spin isomorphism
-- or an Agda kernel receipt. No unsafe pragmas or ESD edits.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (_,_)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans)

import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Algebra.BalancedTernary as Trit
import DASHI.Cognition.RecursiveFibreTower as Tower
import DASHI.Mathematics.Topology.AlexanderHornedNativeBalancedTernaryEndTowerExact as End
import DASHI.Mathematics.Topology.AlexanderHornedNativeTernaryFibreActionExact as Fibre

-- An explicit chain of finite one-child refinements.
data Lift : Nat → Nat → Set where
  stay : ∀ {n} → Lift n n
  step : ∀ {n m} → Lift n m → Lift n (suc m)

liftField : ∀ {n m} → Lift n m →
  Fibre.FibreAction n → Fibre.FibreAction m
liftField stay f = f
liftField (step {m = m} p) f = Fibre.pullback m (liftField p f)

liftInvariant : ∀ {n m} (p : Lift n m)
  (f : Fibre.FibreAction n) →
  Fibre.SectorSignInvariant f →
  Fibre.SectorSignInvariant (liftField p f)
liftInvariant stay f inv = inv
liftInvariant (step {m = m} p) f inv =
  Fibre.invariantsPullback m (liftField p f) (liftInvariant p f inv)

liftEval : ∀ {n m} (p : Lift n m)
  (f : Fibre.FibreAction n) (end : End.BalancedEndPoint) →
  Fibre.evalLocal (Fibre.liftLocal m (liftField p f)) end ≡
    Fibre.evalLocal (Fibre.liftLocal n f) end
liftEval stay f end = refl
liftEval (step {m = m} p) f end =
  trans
    (Fibre.refinementEvaluation m (liftField p f) end)
    (liftEval p f end)

extendLift : ∀ {n m} → Lift n m → Lift (suc n) (suc m)
extendLift stay = stay
extendLift (step p) = step (extendLift p)

liftFromRoot : (m : Nat) → Lift zero m
liftFromRoot zero = stay
liftFromRoot (suc m) = step (liftFromRoot m)

record CommonDepth (n m : Nat) : Set where
  constructor commonAt
  field
    target : Nat
    left : Lift n target
    right : Lift m target
open CommonDepth public

commonDepth : (n m : Nat) → CommonDepth n m
commonDepth zero m = commonAt m (liftFromRoot m) stay
commonDepth (suc n) zero = commonAt (suc n) stay (liftFromRoot (suc n))
commonDepth (suc n) (suc m) with commonDepth n m
... | commonAt k p q = commonAt (suc k) (extendLift p) (extendLift q)

-- Do not redefine Fibre.FibreAction: just package the ORIGINAL proof.
record InvariantCylinder : Set where
  constructor invariantCylinder
  field
    depth : Nat
    fieldAt : Fibre.FibreAction depth
    invariant : Fibre.SectorSignInvariant fieldAt
open InvariantCylinder public

evaluate : InvariantCylinder → End.BalancedEndPoint → C3.C3
evaluate (invariantCylinder n f inv) end =
  Fibre.evalLocal (Fibre.liftLocal n f) end

SameOnEnds : InvariantCylinder → InvariantCylinder → Set
SameOnEnds a b = ∀ end → evaluate a end ≡ evaluate b end

sameReflexive : ∀ a → SameOnEnds a a
sameReflexive a end = refl

sameSymmetric : ∀ a b → SameOnEnds a b → SameOnEnds b a
sameSymmetric a b equal end = sym (equal end)

sameTransitive : ∀ a b c →
  SameOnEnds a b → SameOnEnds b c → SameOnEnds a c
sameTransitive a b c ab bc end = trans (ab end) (bc end)

invariantCombine : ∀ {n} (f g : Fibre.FibreAction n) →
  Fibre.SectorSignInvariant f →
  Fibre.SectorSignInvariant g →
  Fibre.SectorSignInvariant (Fibre.combine f g)
invariantCombine f g fi gi = record
  { sector = λ x → cong₂ C3._∙_
       (Fibre.SectorSignInvariant.sector fi x)
       (Fibre.SectorSignInvariant.sector gi x)
  ; sign = λ x → cong₂ C3._∙_
       (Fibre.SectorSignInvariant.sign fi x)
       (Fibre.SectorSignInvariant.sign gi x)
  }

invariantInverse : ∀ {n} (f : Fibre.FibreAction n) →
  Fibre.SectorSignInvariant f →
  Fibre.SectorSignInvariant (Fibre.inverseAction f)
invariantInverse f fi = record
  { sector = λ x → cong C3.inverse
       (Fibre.SectorSignInvariant.sector fi x)
  ; sign = λ x → cong C3.inverse
       (Fibre.SectorSignInvariant.sign fi x)
  }

combineCylinder : InvariantCylinder → InvariantCylinder →
  InvariantCylinder
combineCylinder (invariantCylinder n f fi)
                (invariantCylinder m g gi)
  with commonDepth n m
... | commonAt k p q =
  invariantCylinder k
    (Fibre.combine (liftField p f) (liftField q g))
    (invariantCombine (liftField p f) (liftField q g)
       (liftInvariant p f fi) (liftInvariant q g gi))

unitCylinder : InvariantCylinder
unitCylinder =
  invariantCylinder zero Fibre.identityAction record
    { sector = λ x → refl
    ; sign = λ x → refl
    }

inverseCylinder : InvariantCylinder → InvariantCylinder
inverseCylinder (invariantCylinder n f inv) =
  invariantCylinder n (Fibre.inverseAction f) (invariantInverse f inv)

evaluateCombine : ∀ a b end →
  evaluate (combineCylinder a b) end ≡
  C3._∙_ (evaluate a end) (evaluate b end)
evaluateCombine (invariantCylinder n f fi)
                (invariantCylinder m g gi) end
  with commonDepth n m
... | commonAt k p q =
  cong₂ C3._∙_ (liftEval p f end) (liftEval q g end)

evaluateInverse : ∀ a end →
  evaluate (inverseCylinder a) end ≡ C3.inverse (evaluate a end)
evaluateInverse (invariantCylinder n f inv) end = refl

evaluateUnit : ∀ end → evaluate unitCylinder end ≡ C3.c0
evaluateUnit end = refl

combineCongruence : ∀ a a' b b' →
  SameOnEnds a a' → SameOnEnds b b' →
  SameOnEnds (combineCylinder a b) (combineCylinder a' b')
combineCongruence a a' b b' aa bb end =
  trans (evaluateCombine a b end)
    (trans (cong₂ C3._∙_ (aa end) (bb end))
       (sym (evaluateCombine a' b' end)))

inverseCongruence : ∀ a b →
  SameOnEnds a b →
  SameOnEnds (inverseCylinder a) (inverseCylinder b)
inverseCongruence a b equal end =
  trans (evaluateInverse a end)
    (trans (cong C3.inverse (equal end))
      (sym (evaluateInverse b end)))

combineAssociativeOnEnds : ∀ a b c →
  SameOnEnds (combineCylinder (combineCylinder a b) c)
             (combineCylinder a (combineCylinder b c))
combineAssociativeOnEnds a b c end =
  trans (evaluateCombine (combineCylinder a b) c end)
    (trans
      (cong (λ z → C3._∙_ z (evaluate c end))
        (evaluateCombine a b end))
      (trans
        (C3.associative (evaluate a end) (evaluate b end)
          (evaluate c end))
        (trans
          (cong (C3._∙_ (evaluate a end))
            (sym (evaluateCombine b c end)))
          (sym (evaluateCombine a (combineCylinder b c) end)))))

combineLeftUnitOnEnds : ∀ a →
  SameOnEnds (combineCylinder unitCylinder a) a
combineLeftUnitOnEnds a end =
  trans (evaluateCombine unitCylinder a end)
    (trans (cong (λ z → C3._∙_ z (evaluate a end))
             (evaluateUnit end))
           (C3.leftIdentity (evaluate a end)))

combineRightUnitOnEnds : ∀ a →
  SameOnEnds (combineCylinder a unitCylinder) a
combineRightUnitOnEnds a end =
  trans (evaluateCombine a unitCylinder end)
    (trans (cong (C3._∙_ (evaluate a end)) (evaluateUnit end))
           (C3.rightIdentity (evaluate a end)))

combineLeftInverseOnEnds : ∀ a →
  SameOnEnds (combineCylinder (inverseCylinder a) a) unitCylinder
combineLeftInverseOnEnds a end =
  trans (evaluateCombine (inverseCylinder a) a end)
    (trans
      (cong (λ z → C3._∙_ z (evaluate a end))
        (evaluateInverse a end))
      (trans (C3.inverseLeft (evaluate a end)) (sym (evaluateUnit end))))

combineRightInverseOnEnds : ∀ a →
  SameOnEnds (combineCylinder a (inverseCylinder a)) unitCylinder
combineRightInverseOnEnds a end =
  trans (evaluateCombine a (inverseCylinder a) end)
    (trans
      (cong (C3._∙_ (evaluate a end)) (evaluateInverse a end))
      (trans (C3.inverseRight (evaluate a end)) (sym (evaluateUnit end))))

-- Construct a CANONICAL INFINITE END extending every finite prefix.
-- This is the missing surjectivity argument for each level projection.
overlay : ∀ {n k} → Vec Trit.Trit n → Vec Trit.Trit k → Vec Trit.Trit k
overlay [] ys = ys
overlay (x ∷ xs) [] = []
overlay (x ∷ xs) (y ∷ ys) = x ∷ overlay xs ys

overlayDropLast : ∀ {n k}
  (prefix : Vec Trit.Trit n) (rest : Vec Trit.Trit (suc k)) →
  End.dropLast (overlay prefix rest) ≡
  overlay prefix (End.dropLast rest)
overlayDropLast [] rest = refl
overlayDropLast (x ∷ xs) (y ∷ []) = refl
overlayDropLast (x ∷ xs) (y ∷ z ∷ zs) =
  cong (x ∷_) (overlayDropLast xs (z ∷ zs))

overlaySameLength : ∀ {n}
  (prefix remainder : Vec Trit.Trit n) →
  overlay prefix remainder ≡ prefix
overlaySameLength [] [] = refl
overlaySameLength (x ∷ xs) (y ∷ ys) =
  cong (x ∷_) (overlaySameLength xs ys)

extendEnd : (n : Nat) → End.BalancedLevel n → End.BalancedEndPoint
extendEnd n (sector , prefix) = record
  { stateAt = λ k → sector , overlay prefix (End.zeroWord k)
  ; coherent = λ k →
      cong (λ ys → (sector , ys))
        (trans
          (overlayDropLast prefix (End.zeroWord (suc k)))
          (cong (overlay prefix) (End.zeroWordProjects k)))
  }

extendEndAt : (n : Nat) (x : End.BalancedLevel n) →
  Tower.stateAt (extendEnd n x) n ≡ x
extendEndAt n (sector , prefix) =
  cong (λ ys → (sector , ys))
    (overlaySameLength prefix (End.zeroWord n))

-- The direct-system equality is existential equality at a common stage.
record EventuallyEqual (a b : InvariantCylinder) : Set where
  constructor eventual
  field
    common : Nat
    leftLift : Lift (depth a) common
    rightLift : Lift (depth b) common
    equalAt : ∀ x →
      liftField leftLift (fieldAt a) x ≡
      liftField rightLift (fieldAt b) x
open EventuallyEqual public

eventualImpliesSameOnEnds : ∀ a b →
  EventuallyEqual a b → SameOnEnds a b
eventualImpliesSameOnEnds
   (invariantCylinder n f fi) (invariantCylinder m g gi)
   (eventual k p q equal) end =
  trans (sym (liftEval p f end))
    (trans (equal (Tower.stateAt end k))
           (liftEval q g end))

sameOnEndsImpliesEventual : ∀ a b →
  SameOnEnds a b → EventuallyEqual a b
sameOnEndsImpliesEventual
  (invariantCylinder n f fi) (invariantCylinder m g gi) equal
  with commonDepth n m
... | commonAt k p q =
  eventual k p q (λ x →
    trans
      (sym (cong (liftField p f) (extendEndAt k x)))
      (trans
        (liftEval p f (extendEnd k x))
        (trans
          (equal (extendEnd k x))
          (trans
            (sym (liftEval q g (extendEnd k x)))
            (cong (liftField q g) (extendEndAt k x))))))

-- The algebraic filtered direct limit is therefore specified by a
-- concrete setoid. A quotient *type* and the compactness argument that
-- ALL continuous K3->C3 maps factor through some finite stage remain
-- independent, not smuggled in as a source-written proof.
