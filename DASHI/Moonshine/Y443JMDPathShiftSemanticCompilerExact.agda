module DASHI.Moonshine.Y443JMDPathShiftSemanticCompilerExact where

------------------------------------------------------------------------
-- The eleven ACTUAL source Coxeter-path conjugation equalities are
-- derived from the 141 exact native finite rewrite steps.
--
-- There are only THREE kinds of group hypotheses, indexed by the
-- source Y443 graph: squares, nonedge commutations and adjacent braids.
-- Source-specific local law providers must derive these from the
-- selected 80 relator words; no "pathShift" assumption remains here.
--
-- Reversing a path word agrees with group inversion because each node
-- is its own inverse. Both group interpretation and proof are on the
-- existing TM.GroupWithInverse, not a model-only permutation group.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
import DASHI.Moonshine.Y443CoxeterPresentationExact as Y
import DASHI.Moonshine.Y443JMDThreePathFiniteRewriteExact as Finite
import DASHI.Moonshine.Y443JMDAllTwelveNodeWordCompilerExact as All
import DASHI.Moonshine.Y443JMDSourceWordInstantiationExact as JMD
import DASHI.Moonshine.Y443JMDPowerFiveSixAlgebraExact as Algebra
import DASHI.Moonshine.Y443JMDNonadjacentRelatorConsequencesExact as Relations
import DASHI.Moonshine.Y443VNaturalPairGenerationExact as Pair
import DASHI.Moonshine.Y443JMDBetaFiveFiniteRewriteExact as W
import DASHI.Moonshine.TwistedModuleModularity as TM

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl eq = eq

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C)
  {x y : A} {z w : B} → x ≡ y → z ≡ w → f x z ≡ f y w
cong₂ f refl refl = refl

record GraphCoxeterGroupLaws
  {G : Set} (gi : TM.GroupWithInverse G)
  (nodes : Y.Node → G) : Set where
  field
    square :
      (x : Y.Node) →
      Pair.multiply gi (nodes x) (nodes x) ≡ Pair.identity gi
    commute :
      (x y : Y.Node) →
      Finite.canCommute x y ≡ true →
      Pair.multiply gi (nodes x) (nodes y)
      ≡ Pair.multiply gi (nodes y) (nodes x)
    braid :
      (x y z : Y.Node) →
      Finite.canBraid x y z ≡ true →
      Pair.multiply gi (nodes x)
        (Pair.multiply gi (nodes y) (nodes z))
      ≡ Pair.multiply gi (nodes y)
        (Pair.multiply gi (nodes x) (nodes y))

open GraphCoxeterGroupLaws public

module Semantic
  {G : Set} (gi : TM.GroupWithInverse G)
  (nodes : Y.Node → G)
  (all : Pair.RelatorsSatisfied gi nodes Y.monsterRelators)
  (laws : GraphCoxeterGroupLaws gi nodes) where

  module A = Algebra.PowerAlgebra gi
  module R = Relations.SourceConsequences gi nodes all
  open A using (e; mul; inv; assoc; leftId; rightId; pow)

  eval : Y.Word → G
  eval = Pair.evaluateCoxeterWord gi nodes

  -- Rooted semantics: every valid finite rewrite is valid in the same
  -- selected group, not just in the free Coxeter string algebra.
  localSound :
    (rule : W.Kind) (word : Y.Word) →
    eval word ≡ eval (Finite.rewriteLocal rule word)
  localSound W.cancel (a ∷ b ∷ rest)
    with Finite.eqNode a b in condition
  ... | true =
    trans
      (sym (assoc (nodes a) (nodes b) (eval rest)))
      (trans
        (cong (λ q → mul q (eval rest))
          (sourceSquareWhenSame a b condition))
        (leftId (eval rest)))
  ... | false = refl
  localSound W.commute (a ∷ b ∷ rest)
    with Finite.canCommute a b in condition
  ... | true =
    trans
      (sym (assoc (nodes a) (nodes b) (eval rest)))
      (trans
        (cong (λ q → mul q (eval rest))
          (commute laws a b condition))
        (assoc (nodes b) (nodes a) (eval rest)))
  ... | false = refl
  localSound W.braid (a ∷ b ∷ c ∷ rest)
    with Finite.canBraid a b c in condition
  ... | true =
    trans
      (cong (mul (nodes a))
        (sym (assoc (nodes b) (nodes c) (eval rest))))
      (trans
        (sym (assoc (nodes a) (mul (nodes b) (nodes c)) (eval rest)))
        (trans
          (cong (λ q → mul q (eval rest))
            (braid laws a b c condition))
          (trans
            (assoc (nodes b) (mul (nodes a) (nodes b)) (eval rest))
            (cong (mul (nodes b))
              (assoc (nodes a) (nodes b) (eval rest))))))
  ... | false = refl
  localSound _ _ = refl

  sourceSquareWhenSame :
    (x y : Y.Node) → Finite.eqNode x y ≡ true →
    mul (nodes x) (nodes y) ≡ e
  sourceSquareWhenSame Y.a Y.a refl = square laws Y.a
  sourceSquareWhenSame Y.b1 Y.b1 refl = square laws Y.b1
  sourceSquareWhenSame Y.c1 Y.c1 refl = square laws Y.c1
  sourceSquareWhenSame Y.d1 Y.d1 refl = square laws Y.d1
  sourceSquareWhenSame Y.e1 Y.e1 refl = square laws Y.e1
  sourceSquareWhenSame Y.b2 Y.b2 refl = square laws Y.b2
  sourceSquareWhenSame Y.c2 Y.c2 refl = square laws Y.c2
  sourceSquareWhenSame Y.d2 Y.d2 refl = square laws Y.d2
  sourceSquareWhenSame Y.e2 Y.e2 refl = square laws Y.e2
  sourceSquareWhenSame Y.b3 Y.b3 refl = square laws Y.b3
  sourceSquareWhenSame Y.c3 Y.c3 refl = square laws Y.c3
  sourceSquareWhenSame Y.d3 Y.d3 refl = square laws Y.d3
  sourceSquareWhenSame Y.a Y.b1 ()
  sourceSquareWhenSame Y.a Y.c1 ()
  sourceSquareWhenSame Y.a Y.d1 ()
  sourceSquareWhenSame Y.a Y.e1 ()
  sourceSquareWhenSame Y.a Y.b2 ()
  sourceSquareWhenSame Y.a Y.c2 ()
  sourceSquareWhenSame Y.a Y.d2 ()
  sourceSquareWhenSame Y.a Y.e2 ()
  sourceSquareWhenSame Y.a Y.b3 ()
  sourceSquareWhenSame Y.a Y.c3 ()
  sourceSquareWhenSame Y.a Y.d3 ()
  sourceSquareWhenSame Y.b1 Y.a ()
  sourceSquareWhenSame Y.b1 Y.c1 ()
  sourceSquareWhenSame Y.b1 Y.d1 ()
  sourceSquareWhenSame Y.b1 Y.e1 ()
  sourceSquareWhenSame Y.b1 Y.b2 ()
  sourceSquareWhenSame Y.b1 Y.c2 ()
  sourceSquareWhenSame Y.b1 Y.d2 ()
  sourceSquareWhenSame Y.b1 Y.e2 ()
  sourceSquareWhenSame Y.b1 Y.b3 ()
  sourceSquareWhenSame Y.b1 Y.c3 ()
  sourceSquareWhenSame Y.b1 Y.d3 ()
  sourceSquareWhenSame Y.c1 Y.a ()
  sourceSquareWhenSame Y.c1 Y.b1 ()
  sourceSquareWhenSame Y.c1 Y.d1 ()
  sourceSquareWhenSame Y.c1 Y.e1 ()
  sourceSquareWhenSame Y.c1 Y.b2 ()
  sourceSquareWhenSame Y.c1 Y.c2 ()
  sourceSquareWhenSame Y.c1 Y.d2 ()
  sourceSquareWhenSame Y.c1 Y.e2 ()
  sourceSquareWhenSame Y.c1 Y.b3 ()
  sourceSquareWhenSame Y.c1 Y.c3 ()
  sourceSquareWhenSame Y.c1 Y.d3 ()
  sourceSquareWhenSame Y.d1 Y.a ()
  sourceSquareWhenSame Y.d1 Y.b1 ()
  sourceSquareWhenSame Y.d1 Y.c1 ()
  sourceSquareWhenSame Y.d1 Y.e1 ()
  sourceSquareWhenSame Y.d1 Y.b2 ()
  sourceSquareWhenSame Y.d1 Y.c2 ()
  sourceSquareWhenSame Y.d1 Y.d2 ()
  sourceSquareWhenSame Y.d1 Y.e2 ()
  sourceSquareWhenSame Y.d1 Y.b3 ()
  sourceSquareWhenSame Y.d1 Y.c3 ()
  sourceSquareWhenSame Y.d1 Y.d3 ()
  sourceSquareWhenSame Y.e1 Y.a ()
  sourceSquareWhenSame Y.e1 Y.b1 ()
  sourceSquareWhenSame Y.e1 Y.c1 ()
  sourceSquareWhenSame Y.e1 Y.d1 ()
  sourceSquareWhenSame Y.e1 Y.b2 ()
  sourceSquareWhenSame Y.e1 Y.c2 ()
  sourceSquareWhenSame Y.e1 Y.d2 ()
  sourceSquareWhenSame Y.e1 Y.e2 ()
  sourceSquareWhenSame Y.e1 Y.b3 ()
  sourceSquareWhenSame Y.e1 Y.c3 ()
  sourceSquareWhenSame Y.e1 Y.d3 ()
  sourceSquareWhenSame Y.b2 Y.a ()
  sourceSquareWhenSame Y.b2 Y.b1 ()
  sourceSquareWhenSame Y.b2 Y.c1 ()
  sourceSquareWhenSame Y.b2 Y.d1 ()
  sourceSquareWhenSame Y.b2 Y.e1 ()
  sourceSquareWhenSame Y.b2 Y.c2 ()
  sourceSquareWhenSame Y.b2 Y.d2 ()
  sourceSquareWhenSame Y.b2 Y.e2 ()
  sourceSquareWhenSame Y.b2 Y.b3 ()
  sourceSquareWhenSame Y.b2 Y.c3 ()
  sourceSquareWhenSame Y.b2 Y.d3 ()
  sourceSquareWhenSame Y.c2 Y.a ()
  sourceSquareWhenSame Y.c2 Y.b1 ()
  sourceSquareWhenSame Y.c2 Y.c1 ()
  sourceSquareWhenSame Y.c2 Y.d1 ()
  sourceSquareWhenSame Y.c2 Y.e1 ()
  sourceSquareWhenSame Y.c2 Y.b2 ()
  sourceSquareWhenSame Y.c2 Y.d2 ()
  sourceSquareWhenSame Y.c2 Y.e2 ()
  sourceSquareWhenSame Y.c2 Y.b3 ()
  sourceSquareWhenSame Y.c2 Y.c3 ()
  sourceSquareWhenSame Y.c2 Y.d3 ()
  sourceSquareWhenSame Y.d2 Y.a ()
  sourceSquareWhenSame Y.d2 Y.b1 ()
  sourceSquareWhenSame Y.d2 Y.c1 ()
  sourceSquareWhenSame Y.d2 Y.d1 ()
  sourceSquareWhenSame Y.d2 Y.e1 ()
  sourceSquareWhenSame Y.d2 Y.b2 ()
  sourceSquareWhenSame Y.d2 Y.c2 ()
  sourceSquareWhenSame Y.d2 Y.e2 ()
  sourceSquareWhenSame Y.d2 Y.b3 ()
  sourceSquareWhenSame Y.d2 Y.c3 ()
  sourceSquareWhenSame Y.d2 Y.d3 ()
  sourceSquareWhenSame Y.e2 Y.a ()
  sourceSquareWhenSame Y.e2 Y.b1 ()
  sourceSquareWhenSame Y.e2 Y.c1 ()
  sourceSquareWhenSame Y.e2 Y.d1 ()
  sourceSquareWhenSame Y.e2 Y.e1 ()
  sourceSquareWhenSame Y.e2 Y.b2 ()
  sourceSquareWhenSame Y.e2 Y.c2 ()
  sourceSquareWhenSame Y.e2 Y.d2 ()
  sourceSquareWhenSame Y.e2 Y.b3 ()
  sourceSquareWhenSame Y.e2 Y.c3 ()
  sourceSquareWhenSame Y.e2 Y.d3 ()
  sourceSquareWhenSame Y.b3 Y.a ()
  sourceSquareWhenSame Y.b3 Y.b1 ()
  sourceSquareWhenSame Y.b3 Y.c1 ()
  sourceSquareWhenSame Y.b3 Y.d1 ()
  sourceSquareWhenSame Y.b3 Y.e1 ()
  sourceSquareWhenSame Y.b3 Y.b2 ()
  sourceSquareWhenSame Y.b3 Y.c2 ()
  sourceSquareWhenSame Y.b3 Y.d2 ()
  sourceSquareWhenSame Y.b3 Y.e2 ()
  sourceSquareWhenSame Y.b3 Y.c3 ()
  sourceSquareWhenSame Y.b3 Y.d3 ()
  sourceSquareWhenSame Y.c3 Y.a ()
  sourceSquareWhenSame Y.c3 Y.b1 ()
  sourceSquareWhenSame Y.c3 Y.c1 ()
  sourceSquareWhenSame Y.c3 Y.d1 ()
  sourceSquareWhenSame Y.c3 Y.e1 ()
  sourceSquareWhenSame Y.c3 Y.b2 ()
  sourceSquareWhenSame Y.c3 Y.c2 ()
  sourceSquareWhenSame Y.c3 Y.d2 ()
  sourceSquareWhenSame Y.c3 Y.e2 ()
  sourceSquareWhenSame Y.c3 Y.b3 ()
  sourceSquareWhenSame Y.c3 Y.d3 ()
  sourceSquareWhenSame Y.d3 Y.a ()
  sourceSquareWhenSame Y.d3 Y.b1 ()
  sourceSquareWhenSame Y.d3 Y.c1 ()
  sourceSquareWhenSame Y.d3 Y.d1 ()
  sourceSquareWhenSame Y.d3 Y.e1 ()
  sourceSquareWhenSame Y.d3 Y.b2 ()
  sourceSquareWhenSame Y.d3 Y.c2 ()
  sourceSquareWhenSame Y.d3 Y.d2 ()
  sourceSquareWhenSame Y.d3 Y.e2 ()
  sourceSquareWhenSame Y.d3 Y.b3 ()
  sourceSquareWhenSame Y.d3 Y.c3 ()

  stepAtSound :
    (n : Nat) (rule : W.Kind) (word : Y.Word) →
    eval word ≡ eval (Finite.stepAt n rule word)
  stepAtSound zero rule word = localSound rule word
  stepAtSound (suc n) rule [] = refl
  stepAtSound (suc n) rule (x ∷ xs) =
    cong (mul (nodes x)) (stepAtSound n rule xs)

  runSound :
    (word : Y.Word) (ops : List W.Operation) →
    eval word ≡ eval (Finite.run word ops)
  runSound word [] = refl
  runSound word (op ∷ ops) =
    trans (stepAtSound (W.position op) (W.kind op) word)
      (runSound (Finite.step op word) ops)

  evalAppend :
    (u v : Y.Word) →
    eval (Y._++_ u v) ≡ mul (eval u) (eval v)
  evalAppend [] v = sym (leftId (eval v))
  evalAppend (x ∷ xs) v =
    trans
      (cong (mul (nodes x)) (evalAppend xs v))
      (sym (assoc (nodes x) (eval xs) (eval v)))

  single : (n : Y.Node) → eval (n ∷ []) ≡ nodes n
  single n = rightId (nodes n)

  evalReverse :
    (w : Y.Word) →
    eval (Finite.reverse w) ≡ inv (eval w)
  evalReverse [] = R.leftInverseUnique e e (leftId e)
  evalReverse (x ∷ rest) =
    trans
      (evalAppend (Finite.reverse rest) (x ∷ []))
      (trans
        (cong₂ mul (evalReverse rest) (single x))
        (trans
          (cong (mul (inv (eval rest)))
            (R.leftInverseUnique (nodes x) (nodes x)
              (square laws x)))
          (R.inverseProduct (nodes x) (eval rest))))

  evalBackwardWord :
    (i : Nat) →
    eval (Finite.backwardWord i) ≡
    mul
      (mul (inv (JMD.uElement gi nodes))
        (nodes (Finite.lookupPath Finite.firstPath (suc i))))
      (JMD.uElement gi nodes)
  evalBackwardWord i =
    trans
      (evalAppend (Finite.reverse JMD.uPath)
        (Y._++_
          (Finite.lookupPath JMD.uPath (suc i) ∷ []) JMD.uPath))
      (trans
        (cong₂ mul (evalReverse JMD.uPath)
          (trans
            (evalAppend
              (Finite.lookupPath JMD.uPath (suc i) ∷ [])
              JMD.uPath)
            (cong (λ z → mul z (eval JMD.uPath))
              (single (Finite.lookupPath JMD.uPath (suc i))))))
        (sym (assoc
          (inv (JMD.uElement gi nodes))
          (nodes (Finite.lookupPath JMD.uPath (suc i)))
          (JMD.uElement gi nodes))))

  evalForwardWord :
    (i : Nat) →
    eval (Finite.forwardWord i) ≡
    mul
      (mul
        (mul (nodes Y.a) (JMD.betaElement gi nodes))
        (nodes (Finite.lookupPath Finite.thirdPath i)))
      (inv (mul (nodes Y.a) (JMD.betaElement gi nodes)))
  evalForwardWord i =
    trans
      (evalAppend JMD.thirdPath
        (Y._++_ (Finite.lookupPath JMD.thirdPath i ∷ [])
          (Finite.reverse JMD.thirdPath)))
      (trans
        (cong₂ mul refl
          (trans
            (evalAppend (Finite.lookupPath JMD.thirdPath i ∷ [])
              (Finite.reverse JMD.thirdPath))
            (cong₂ mul
              (single (Finite.lookupPath JMD.thirdPath i))
              (evalReverse JMD.thirdPath))))
        (sym (assoc
          (mul (nodes Y.a) (JMD.betaElement gi nodes))
          (nodes (Finite.lookupPath JMD.thirdPath i))
          (inv (mul (nodes Y.a) (JMD.betaElement gi nodes))))))

  backwardAt :
    (i : Nat) (ops : List W.Operation) →
    Finite.run (Finite.backwardWord i) ops
      ≡ (Finite.lookupPath Finite.firstPath i ∷ []) →
    nodes (Finite.lookupPath Finite.firstPath i) ≡
    mul
      (mul (inv (JMD.uElement gi nodes))
        (nodes (Finite.lookupPath Finite.firstPath (suc i))))
      (JMD.uElement gi nodes)
  backwardAt i ops result =
    sym
      (trans (sym (evalBackwardWord i))
        (trans (runSound (Finite.backwardWord i) ops)
          (trans (cong eval result)
            (single (Finite.lookupPath Finite.firstPath i)))))

  forwardAt :
    (i : Nat) (ops : List W.Operation) →
    Finite.run (Finite.forwardWord i) ops
      ≡ (Finite.lookupPath Finite.thirdPath (suc i) ∷ []) →
    nodes (Finite.lookupPath Finite.thirdPath (suc i)) ≡
    mul
      (mul
        (mul (nodes Y.a) (JMD.betaElement gi nodes))
        (nodes (Finite.lookupPath Finite.thirdPath i)))
      (inv (mul (nodes Y.a) (JMD.betaElement gi nodes)))
  forwardAt i ops result =
    sym
      (trans (sym (evalForwardWord i))
        (trans (runSound (Finite.forwardWord i) ops)
          (trans (cong eval result)
            (single (Finite.lookupPath Finite.thirdPath (suc i))))))

  elevenSourcePathShiftEquations :
    All.JMDPathShiftCertificate gi nodes
  elevenSourcePathShiftEquations =
    record
      { All.d1FromE1 = backwardAt 6 Finite.pathP1Shift6 Finite.pathP1Shift6Result
      ; All.c1FromD1 = backwardAt 5 Finite.pathP1Shift5 Finite.pathP1Shift5Result
      ; All.b1FromC1 = backwardAt 4 Finite.pathP1Shift4 Finite.pathP1Shift4Result
      ; All.aFromB1 = backwardAt 3 Finite.pathP1Shift3 Finite.pathP1Shift3Result
      ; All.b3FromA = backwardAt 2 Finite.pathP1Shift2 Finite.pathP1Shift2Result
      ; All.c3FromB3 = backwardAt 1 Finite.pathP1Shift1 Finite.pathP1Shift1Result
      ; All.d3FromC3 = backwardAt 0 Finite.pathP1Shift0 Finite.pathP1Shift0Result
      ; All.b2FromA = forwardAt 0 Finite.pathP3Shift0 Finite.pathP3Shift0Result
      ; All.c2FromB2 = forwardAt 1 Finite.pathP3Shift1 Finite.pathP3Shift1Result
      ; All.d2FromC2 = forwardAt 2 Finite.pathP3Shift2 Finite.pathP3Shift2Result
      ; All.e2FromD2 = forwardAt 3 Finite.pathP3Shift3 Finite.pathP3Shift3Result
      }
