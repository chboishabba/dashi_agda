module DASHI.Moonshine.Y443JMDAllTwelveNodeWordCompilerExact where

------------------------------------------------------------------------
-- JMD ORIGINAL THREE-PATH ALL-TWELVE NODE RECOVERY.
--
-- The Lean source y443_closure_pair_eq_top reconstructs all twelve
-- nodes using path Coxeter conjugation. This Agda module performs the
-- complete constructive extraction once the 11 specific path-shift
-- identities are supplied on the SAME Y443 presented group.
--
-- Source paths:
--  P1 = [d3,c3,b3,a,b1,c1,d1,e1],  c1 = u
--  P3 = [a,b2,c2,d2,e2],          c3 = a*beta
--
-- From x4=e1 in <u,v>, shift BACK along P1 through all eight nodes.
-- From a=x0 in <u,v>, shift FORWARD along P3 for b2,c2,d2,e2.
-- This yields all 12 concrete u/v syntax trees, not a blanket
-- axiom "all nodes lie in the pair subgroup".
--
-- Only the Coxeter-path conjugation identities are producer inputs.
-- Do not mistake this compiler for a native Agda proof of those
-- identities from source m2/m3 relations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Moonshine.Y443CoxeterPresentationExact as Y
import DASHI.Moonshine.Y443VNaturalPairGenerationExact as Pair
import DASHI.Moonshine.Y443JMDSourceWordInstantiationExact as Source
import DASHI.Moonshine.Y443JMDA4RulesFromPresentationExact as Initial
import DASHI.Moonshine.Y443JMDTracePowerExact as Trace
import DASHI.Moonshine.TwistedModuleModularity as TM

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl eq = eq

------------------------------------------------------------------------
-- Equations in the selected SAME source group.
------------------------------------------------------------------------

record JMDPathShiftCertificate
  {G : Set} (gi : TM.GroupWithInverse G)
  (nodes : Y.Node → G) : Set where
  field
    -- P1 backwards under u: earlier = u^-1 * later * u.
    d1FromE1 :
      nodes Y.d1 ≡
      Pair.multiply gi
        (Pair.multiply gi (Pair.inverse gi (Source.uElement gi nodes))
          (nodes Y.e1)) (Source.uElement gi nodes)
    c1FromD1 :
      nodes Y.c1 ≡
      Pair.multiply gi
        (Pair.multiply gi (Pair.inverse gi (Source.uElement gi nodes))
          (nodes Y.d1)) (Source.uElement gi nodes)
    b1FromC1 :
      nodes Y.b1 ≡
      Pair.multiply gi
        (Pair.multiply gi (Pair.inverse gi (Source.uElement gi nodes))
          (nodes Y.c1)) (Source.uElement gi nodes)
    aFromB1 :
      nodes Y.a ≡
      Pair.multiply gi
        (Pair.multiply gi (Pair.inverse gi (Source.uElement gi nodes))
          (nodes Y.b1)) (Source.uElement gi nodes)
    b3FromA :
      nodes Y.b3 ≡
      Pair.multiply gi
        (Pair.multiply gi (Pair.inverse gi (Source.uElement gi nodes))
          (nodes Y.a)) (Source.uElement gi nodes)
    c3FromB3 :
      nodes Y.c3 ≡
      Pair.multiply gi
        (Pair.multiply gi (Pair.inverse gi (Source.uElement gi nodes))
          (nodes Y.b3)) (Source.uElement gi nodes)
    d3FromC3 :
      nodes Y.d3 ≡
      Pair.multiply gi
        (Pair.multiply gi (Pair.inverse gi (Source.uElement gi nodes))
          (nodes Y.c3)) (Source.uElement gi nodes)

    -- P3 forwards under a*beta: later = c3 * earlier * c3^-1.
    b2FromA :
      nodes Y.b2 ≡
      Pair.multiply gi
        (Pair.multiply gi
          (Pair.multiply gi (nodes Y.a) (Source.betaElement gi nodes))
          (nodes Y.a))
        (Pair.inverse gi
          (Pair.multiply gi (nodes Y.a) (Source.betaElement gi nodes)))
    c2FromB2 :
      nodes Y.c2 ≡
      Pair.multiply gi
        (Pair.multiply gi
          (Pair.multiply gi (nodes Y.a) (Source.betaElement gi nodes))
          (nodes Y.b2))
        (Pair.inverse gi
          (Pair.multiply gi (nodes Y.a) (Source.betaElement gi nodes)))
    d2FromC2 :
      nodes Y.d2 ≡
      Pair.multiply gi
        (Pair.multiply gi
          (Pair.multiply gi (nodes Y.a) (Source.betaElement gi nodes))
          (nodes Y.c2))
        (Pair.inverse gi
          (Pair.multiply gi (nodes Y.a) (Source.betaElement gi nodes)))
    e2FromD2 :
      nodes Y.e2 ≡
      Pair.multiply gi
        (Pair.multiply gi
          (Pair.multiply gi (nodes Y.a) (Source.betaElement gi nodes))
          (nodes Y.d2))
        (Pair.inverse gi
          (Pair.multiply gi (nodes Y.a) (Source.betaElement gi nodes)))

open JMDPathShiftCertificate public

------------------------------------------------------------------------
-- Generic closure under conjugation, producing actual word syntax trees.
------------------------------------------------------------------------

conjugatedRepresented :
  ∀ {G} (gi : TM.GroupWithInverse G) (u v c x : G) →
  Pair.RepresentedByPair gi u v c →
  Pair.RepresentedByPair gi u v x →
  Pair.RepresentedByPair gi u v
    (Pair.multiply gi
      (Pair.multiply gi (Pair.inverse gi c) x) c)
conjugatedRepresented gi u v c x pc px =
  Pair.productRepresented gi u v
    (Pair.multiply gi (Pair.inverse gi c) x) c
    (Pair.productRepresented gi u v (Pair.inverse gi c) x
      (Pair.inverseRepresented gi u v c pc) px)
    pc

forwardConjugatedRepresented :
  ∀ {G} (gi : TM.GroupWithInverse G) (u v c x : G) →
  Pair.RepresentedByPair gi u v c →
  Pair.RepresentedByPair gi u v x →
  Pair.RepresentedByPair gi u v
    (Pair.multiply gi
      (Pair.multiply gi c x) (Pair.inverse gi c))
forwardConjugatedRepresented gi u v c x pc px =
  Pair.productRepresented gi u v
    (Pair.multiply gi c x) (Pair.inverse gi c)
    (Pair.productRepresented gi u v c x pc px)
    (Pair.inverseRepresented gi u v c pc)

------------------------------------------------------------------------
-- Real source eight/path and four/path word certificates in one group.
------------------------------------------------------------------------

module Recover {G : Set} (gi : TM.GroupWithInverse G)
  (nodes : Y.Node → G)
  (relators : Pair.RelatorsSatisfied gi nodes Y.monsterRelators)
  (shifts : JMDPathShiftCertificate gi nodes) where

  u : G
  u = Source.uElement gi nodes

  v : G
  v = Source.vElement gi nodes

  beta : G
  beta = Source.betaElement gi nodes

  lift :
    ∀ {x y : G} →
    x ≡ y → Pair.RepresentedByPair gi u v y →
    Pair.RepresentedByPair gi u v x
  lift equality proof = Trace.transportRepresented gi u v
    (sym equality) proof

  uRepresented : Pair.RepresentedByPair gi u v u
  uRepresented = Pair.represented Pair.leftGenerator refl

  betaRepresented : Pair.RepresentedByPair gi u v beta
  betaRepresented =
    Initial.Actual.betaInPairWithNoExtraPowerPremise gi nodes relators

  e1Represented : Pair.RepresentedByPair gi u v (nodes Y.e1)
  e1Represented =
    Initial.Actual.x4InPairWithNoExtraPowerPremise gi nodes relators

  backward :
    ∀ {x y : G} →
    x ≡ Pair.multiply gi
        (Pair.multiply gi (Pair.inverse gi u) y) u →
    Pair.RepresentedByPair gi u v y →
    Pair.RepresentedByPair gi u v x
  backward {y = y} eq witness =
    lift eq
      (conjugatedRepresented gi u v u y uRepresented witness)

  d1Represented : Pair.RepresentedByPair gi u v (nodes Y.d1)
  d1Represented = backward (d1FromE1 shifts) e1Represented

  c1Represented : Pair.RepresentedByPair gi u v (nodes Y.c1)
  c1Represented = backward (c1FromD1 shifts) d1Represented

  b1Represented : Pair.RepresentedByPair gi u v (nodes Y.b1)
  b1Represented = backward (b1FromC1 shifts) c1Represented

  aRepresented : Pair.RepresentedByPair gi u v (nodes Y.a)
  aRepresented = backward (aFromB1 shifts) b1Represented

  b3Represented : Pair.RepresentedByPair gi u v (nodes Y.b3)
  b3Represented = backward (b3FromA shifts) aRepresented

  c3Represented : Pair.RepresentedByPair gi u v (nodes Y.c3)
  c3Represented = backward (c3FromB3 shifts) b3Represented

  d3Represented : Pair.RepresentedByPair gi u v (nodes Y.d3)
  d3Represented = backward (d3FromC3 shifts) c3Represented

  thirdCoxeter : G
  thirdCoxeter = Pair.multiply gi (nodes Y.a) beta

  thirdCoxeterRepresented :
    Pair.RepresentedByPair gi u v thirdCoxeter
  thirdCoxeterRepresented =
    Pair.productRepresented gi u v (nodes Y.a) beta
      aRepresented betaRepresented

  forward :
    ∀ {x y : G} →
    x ≡ Pair.multiply gi
        (Pair.multiply gi thirdCoxeter y)
        (Pair.inverse gi thirdCoxeter) →
    Pair.RepresentedByPair gi u v y →
    Pair.RepresentedByPair gi u v x
  forward {y = y} eq witness =
    lift eq
      (forwardConjugatedRepresented gi u v thirdCoxeter y
        thirdCoxeterRepresented witness)

  b2Represented : Pair.RepresentedByPair gi u v (nodes Y.b2)
  b2Represented = forward (b2FromA shifts) aRepresented

  c2Represented : Pair.RepresentedByPair gi u v (nodes Y.c2)
  c2Represented = forward (c2FromB2 shifts) b2Represented

  d2Represented : Pair.RepresentedByPair gi u v (nodes Y.d2)
  d2Represented = forward (d2FromC2 shifts) c2Represented

  e2Represented : Pair.RepresentedByPair gi u v (nodes Y.e2)
  e2Represented = forward (e2FromD2 shifts) d2Represented

  everyNodeRepresented :
    (n : Y.Node) → Pair.RepresentedByPair gi u v (nodes n)
  everyNodeRepresented Y.a = aRepresented
  everyNodeRepresented Y.b1 = b1Represented
  everyNodeRepresented Y.c1 = c1Represented
  everyNodeRepresented Y.d1 = d1Represented
  everyNodeRepresented Y.e1 = e1Represented
  everyNodeRepresented Y.b2 = b2Represented
  everyNodeRepresented Y.c2 = c2Represented
  everyNodeRepresented Y.d2 = d2Represented
  everyNodeRepresented Y.e2 = e2Represented
  everyNodeRepresented Y.b3 = b3Represented
  everyNodeRepresented Y.c3 = c3Represented
  everyNodeRepresented Y.d3 = d3Represented

  actualNodeWordCertificate : Pair.NodeWordCertificate gi u v nodes
  actualNodeWordCertificate = record
    { Pair.nodeWord = λ n → Pair.word (everyNodeRepresented n)
    ; Pair.nodeWordIdentifies =
        λ n → Pair.interpretation (everyNodeRepresented n)
    }
