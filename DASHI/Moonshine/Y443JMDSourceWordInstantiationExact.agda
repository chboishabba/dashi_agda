module DASHI.Moonshine.Y443JMDSourceWordInstantiationExact where

------------------------------------------------------------------------
-- EXACT TWO-GENERATOR WORDS, FROM THE ORIGINAL JMD LEAN SOURCE.
--
-- Source (James Michael DuPont / meta-introspector):
-- https://github.com/AxiomMath/CFSGCorollary/blob/main/
--   CFSGCorollary/Sporadic/Monster/Y443.lean
--
-- The real Lean owner explicitly proves y443_paths and
-- y443_closure_pair_eq_top (by closure_pair_eq_top_of_paths).
-- The external theorem is NOT silently imported as an Agda proof.
--
-- x0=a, x1=b1,...,x4=e1, x5=b2,...,x8=e2,
-- x9=b3,x10=c3,x11=d3. Thus
-- u = x11*x10*x9*x0*x1*x2*x3*x4
-- beta = x5*x6*x7*x8
-- v = u*x4*beta
-- w = u^{-1}*v = x4*beta.
--
-- This module supplies concrete Agda source words, all 12 node address
-- equalities, and proves w=u^-1*v from existing inverse/associative laws.
-- The path Coxeter generation theorem is still owned by Lean until
-- replayed using actual Agda semantic group instances.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
import DASHI.Moonshine.Y443CoxeterPresentationExact as Y
import DASHI.Moonshine.Y443VNaturalPairGenerationExact as Pair
import DASHI.Moonshine.TwistedModuleModularity as TM
import DASHI.Moonshine.GradedRepresentation as GR

node : Y.Node → Y.Node
node n = n

x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Y.Node
x0 = Y.a
x1 = Y.b1
x2 = Y.c1
x3 = Y.d1
x4 = Y.e1
x5 = Y.b2
x6 = Y.c2
x7 = Y.d2
x8 = Y.e2
x9 = Y.b3
x10 = Y.c3
x11 = Y.d3

uPath : Y.Word
uPath = x11 ∷ x10 ∷ x9 ∷ x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ []

betaPath : Y.Word
betaPath = x5 ∷ x6 ∷ x7 ∷ x8 ∷ []

thirdPath : Y.Word
thirdPath = x0 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ []

uPathHasEight : Y.length uPath ≡ 8
uPathHasEight = refl

betaPathHasFour : Y.length betaPath ≡ 4
betaPathHasFour = refl

thirdPathHasFive : Y.length thirdPath ≡ 5
thirdPathHasFive = refl

-- Semantic evaluation in the same group used by Y443VNaturalPairWeld.
uElement :
  ∀ {G} (gi : TM.GroupWithInverse G) (nodes : Y.Node → G) → G
uElement gi nodes = Pair.evaluateCoxeterWord gi nodes uPath

betaElement :
  ∀ {G} (gi : TM.GroupWithInverse G) (nodes : Y.Node → G) → G
betaElement gi nodes = Pair.evaluateCoxeterWord gi nodes betaPath

vElement :
  ∀ {G} (gi : TM.GroupWithInverse G) (nodes : Y.Node → G) → G
vElement gi nodes =
  Pair.multiply gi
    (Pair.multiply gi (uElement gi nodes) (nodes x4))
    (betaElement gi nodes)

-- The exact source has v = u*x4*beta, and its proof recovers
-- w = u^-1*v before taking the fifth/sixth powers.

wElement :
  ∀ {G} (gi : TM.GroupWithInverse G) (nodes : Y.Node → G) → G
wElement gi nodes =
  Pair.multiply gi
    (Pair.inverse gi (uElement gi nodes))
    (vElement gi nodes)

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

wIsX4Beta :
  ∀ {G} (gi : TM.GroupWithInverse G) (nodes : Y.Node → G) →
  wElement gi nodes ≡
  Pair.multiply gi (nodes x4) (betaElement gi nodes)
wIsX4Beta gi nodes =
  let
    u = uElement gi nodes
    x = nodes x4
    b = betaElement gi nodes
    mult = Pair.multiply gi
    inv = Pair.inverse gi
    g = TM.GroupWithInverse.group gi
  in
  trans
    (GR.Group.associativity g (inv u) (mult u x) b)
    (trans
      (cong (λ z → mult z b)
        (trans
          (GR.Group.associativity g (inv u) u x)
          (trans
            (cong (λ z → mult z x)
              (TM.GroupWithInverse.leftInverse gi u))
            (GR.Group.leftIdentity g x))))
      refl)

-- A literal u/v word for w follows from the same proof.
jmdWTwoWord : Pair.TwoWord
jmdWTwoWord =
  Pair.wordMultiply
    (Pair.wordInverse Pair.leftGenerator)
    Pair.rightGenerator

jmdWFromPair :
  ∀ {G} (gi : TM.GroupWithInverse G) (nodes : Y.Node → G) →
  Pair.RepresentedByPair gi
    (uElement gi nodes) (vElement gi nodes) (wElement gi nodes)
jmdWFromPair gi nodes =
  Pair.represented jmdWTwoWord refl

-- The exact Lean path proposition, when translated to Agda, must provide
-- path-Coxeter recovery and the group-generation property. These are
-- deliberately separate from literal source-word reconstruction.
