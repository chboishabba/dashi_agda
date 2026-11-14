module DASHI.Moonshine.Y443VNaturalPairGenerationExact where

------------------------------------------------------------------------
-- Constructive two-generator word-to-VOA action transport.
--
-- JMD / James Michael DuPont (meta-introspector) owns the external Y443
-- ten-step H = <u,v> generation trace and closure_pair_eq_top_of_paths.
-- Its actual path words and proof term have NOT been supplied to DASHI.
--
-- DASHI CONTRIBUTION:
-- Given a proof that all twelve Y443 nodes have u/v words and the
-- standard node-generation property, construct a word for EVERY group
-- element, not just a Bool receipt. Transport the resulting equality to
-- the EXISTING literal V^natural action (same group and state carrier).
--
-- TauCeti, Ivanov and Bray own the underlying Y443 presentation;
-- Popov--Rastelli own Lean_VOA, an independent VOA construction donor.
-- No new Monster group, VOA, or claimed full automorphism theorem here.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Unit using (⊤)
import DASHI.Moonshine.GradedRepresentation as GR
import DASHI.Moonshine.TwistedModuleModularity as TM
import DASHI.Moonshine.VertexOperatorAlgebraCore as VOA
import DASHI.Moonshine.VNaturalOrbifoldConstruction as VN
import DASHI.Moonshine.Y443CoxeterPresentationExact as Y

------------------------------------------------------------------------
-- Small proof transport helpers, no axioms.
------------------------------------------------------------------------

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ :
  ∀ {A B C : Set} (f : A → B → C) {x y : A} {z w : B} →
  x ≡ y → z ≡ w → f x z ≡ f y w
cong₂ f refl refl = refl

record _∧_ (A B : Set) : Set where
  constructor _,,_
  field
    left : A
    right : B

------------------------------------------------------------------------
-- Same source group throughout: reuse the existing inverse group owner.
------------------------------------------------------------------------

identity : ∀ {G} → TM.GroupWithInverse G → G
identity gi = GR.Group.identity (TM.GroupWithInverse.group gi)

multiply : ∀ {G} → TM.GroupWithInverse G → G → G → G
multiply gi = GR.Group._∙_ (TM.GroupWithInverse.group gi)

inverse : ∀ {G} → TM.GroupWithInverse G → G → G
inverse = TM.GroupWithInverse.inverse

data TwoWord : Set where
  emptyWord : TwoWord
  leftGenerator : TwoWord
  rightGenerator : TwoWord
  wordMultiply : TwoWord → TwoWord → TwoWord
  wordInverse : TwoWord → TwoWord

evaluate :
  ∀ {G} (gi : TM.GroupWithInverse G) (u v : G) →
  TwoWord → G
evaluate gi u v emptyWord = identity gi
evaluate gi u v leftGenerator = u
evaluate gi u v rightGenerator = v
evaluate gi u v (wordMultiply x y) =
  multiply gi (evaluate gi u v x) (evaluate gi u v y)
evaluate gi u v (wordInverse x) =
  inverse gi (evaluate gi u v x)

record RepresentedByPair
  {G : Set} (gi : TM.GroupWithInverse G) (u v x : G) : Set where
  constructor represented
  field
    word : TwoWord
    interpretation : evaluate gi u v word ≡ x

open RepresentedByPair public

identityRepresented :
  ∀ {G} (gi : TM.GroupWithInverse G) (u v : G) →
  RepresentedByPair gi u v (identity gi)
identityRepresented gi u v = represented emptyWord refl

productRepresented :
  ∀ {G} (gi : TM.GroupWithInverse G) (u v x y : G) →
  RepresentedByPair gi u v x →
  RepresentedByPair gi u v y →
  RepresentedByPair gi u v (multiply gi x y)
productRepresented gi u v x y px py =
  represented
    (wordMultiply (word px) (word py))
    (cong₂ (multiply gi) (interpretation px) (interpretation py))

inverseRepresented :
  ∀ {G} (gi : TM.GroupWithInverse G) (u v x : G) →
  RepresentedByPair gi u v x →
  RepresentedByPair gi u v (inverse gi x)
inverseRepresented gi u v x px =
  represented (wordInverse (word px))
    (cong (inverse gi) (interpretation px))

------------------------------------------------------------------------
-- Actual JMD node-word data are premises, not fabricated words.
------------------------------------------------------------------------

record NodeWordCertificate
  {G : Set} (gi : TM.GroupWithInverse G)
  (u v : G) (nodes : Y.Node → G) : Set where
  field
    nodeWord : Y.Node → TwoWord
    nodeWordIdentifies :
      (n : Y.Node) → evaluate gi u v (nodeWord n) ≡ nodes n

open NodeWordCertificate public

-- A standard presentation-generated group has the following universal
-- closure principle. The actual Y443 source witness is required here.
record NodeGeneration
  {G : Set} (gi : TM.GroupWithInverse G)
  (nodes : Y.Node → G) : Set₁ where
  field
    allFromNodes :
      (P : G → Set) →
      P (identity gi) →
      (∀ {x y} → P x → P y → P (multiply gi x y)) →
      (∀ {x} → P x → P (inverse gi x)) →
      ((n : Y.Node) → P (nodes n)) →
      (x : G) → P x

open NodeGeneration public

nodeRepresented :
  ∀ {G} (gi : TM.GroupWithInverse G)
  (u v : G) (nodes : Y.Node → G)
  (certificate : NodeWordCertificate gi u v nodes) →
  (n : Y.Node) → RepresentedByPair gi u v (nodes n)
nodeRepresented gi u v nodes certificate n =
  represented (nodeWord certificate n) (nodeWordIdentifies certificate n)

-- Constructive surjectivity, not merely a proof of membership in H.
pairWordsSurjective :
  ∀ {G} (gi : TM.GroupWithInverse G)
  (u v : G) (nodes : Y.Node → G) →
  NodeWordCertificate gi u v nodes →
  NodeGeneration gi nodes →
  (g : G) → RepresentedByPair gi u v g
pairWordsSurjective gi u v nodes words generated g =
  allFromNodes generated
    (RepresentedByPair gi u v)
    (identityRepresented gi u v)
    (λ {x} {y} px py → productRepresented gi u v x y px py)
    (λ {x} px → inverseRepresented gi u v x px)
    (nodeRepresented gi u v nodes words)
    g

------------------------------------------------------------------------
-- Source presentation relations evaluated in the SAME group carrier.
------------------------------------------------------------------------

evaluateCoxeterWord :
  ∀ {G} (gi : TM.GroupWithInverse G) →
  (Y.Node → G) → Y.Word → G
evaluateCoxeterWord gi nodes [] = identity gi
evaluateCoxeterWord gi nodes (n ∷ rest) =
  multiply gi (nodes n) (evaluateCoxeterWord gi nodes rest)

RelatorsSatisfied :
  ∀ {G} (gi : TM.GroupWithInverse G) →
  (nodes : Y.Node → G) → List Y.Word → Set
RelatorsSatisfied gi nodes [] = ⊤
RelatorsSatisfied gi nodes (w ∷ ws) =
  (evaluateCoxeterWord gi nodes w ≡ identity gi)
  ∧ RelatorsSatisfied gi nodes ws

------------------------------------------------------------------------
-- Actual Vnatural owner, not a fresh VOA or parallel Monster representation.
------------------------------------------------------------------------

record Y443VNaturalPairWeld (G : Set) : Setω where
  field
    groupWithInverse : TM.GroupWithInverse G
    construction : VN.VNaturalConstruction

    voaAction :
      VOA.VOAGroupAction
        G (TM.GroupWithInverse.group groupWithInverse)
        (VN.VNaturalConstruction.Vnatural construction)

    u v : G
    nodes : Y.Node → G
    nodeWordCertificate :
      NodeWordCertificate groupWithInverse u v nodes
    nodesGenerate :
      NodeGeneration groupWithInverse nodes
    y443RelatorsHold :
      RelatorsSatisfied groupWithInverse nodes Y.monsterRelators

  PairWordFor : G → Set
  PairWordFor g =
    RepresentedByPair groupWithInverse u v g

  cover : (g : G) → PairWordFor g
  cover = pairWordsSurjective
    groupWithInverse u v nodes nodeWordCertificate nodesGenerate

open Y443VNaturalPairWeld public

VNaturalState : ∀ {G} → Y443VNaturalPairWeld G → Set
VNaturalState weld =
  VOA.GradedModule.Carrier
    (VOA.VertexOperatorAlgebra.gradedModule
      (VN.VNaturalConstruction.Vnatural (construction weld)))

literalAction :
  ∀ {G} (weld : Y443VNaturalPairWeld G) →
  G → VNaturalState weld → VNaturalState weld
literalAction weld = VOA.VOAGroupAction.act (voaAction weld)

-- Every action of g on the SAME literal Vnatural state can be replaced by
-- the action of an explicit u/v word; no separate action is constructed.
pairWordActionMatchesLiteral :
  ∀ {G} (weld : Y443VNaturalPairWeld G) →
  (g : G) (state : VNaturalState weld) →
  literalAction weld
    (evaluate (groupWithInverse weld) (u weld) (v weld)
      (word (cover weld g))) state
  ≡ literalAction weld g state
pairWordActionMatchesLiteral weld g state =
  cong (λ x → literalAction weld x state)
    (interpretation (cover weld g))
