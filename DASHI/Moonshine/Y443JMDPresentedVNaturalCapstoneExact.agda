module DASHI.Moonshine.Y443JMDPresentedVNaturalCapstoneExact where

------------------------------------------------------------------------
-- SOURCE-EXACT FINITE/PRESENTED JMD TWO-GENERATOR → SAME VOA ACTION.
--
-- No assumed NodeWordCertificate or NodeGeneration:
-- * original eighty relators compile to x4, beta u/v words;
-- * 11 path-Coxeter shift equations compile all twelve node words;
-- * literal presented-group signed-word surjectivity compiles the
--   node-generation induction.
--
-- The selected VOA action is THE EXISTING source's action, not an
-- independently constructed representation. This avoids the previous
-- opaque all-twelve and all-elements witness fields.
--
-- The only remaining external semantic producers:
-- 1. concrete Y443 presentation's signed-word surjectivity;
-- 2. 11 generic Coxeter-path shift equations (Lean source proves them);
-- 3. selection/identification of the actual Monster group action;
-- 4. full VOA automorphism equivalence, not implied by transport.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Moonshine.Y443CoxeterPresentationExact as Y
import DASHI.Moonshine.Y443VNaturalPairGenerationExact as Pair
import DASHI.Moonshine.Y443JMDSourceWordInstantiationExact as Source
import DASHI.Moonshine.Y443JMDAllTwelveNodeWordCompilerExact as All
import DASHI.Moonshine.Y443PresentedGroupNodeGenerationExact as Presented
import DASHI.Moonshine.TwistedModuleModularity as TM
import DASHI.Moonshine.VertexOperatorAlgebraCore as VOA
import DASHI.Moonshine.VNaturalOrbifoldConstruction as VN

record PresentedY443VNaturalSource (G : Set) : Setω where
  field
    groupWithInverse : TM.GroupWithInverse G
    nodes : Y.Node → G
    relatorsHold :
      Pair.RelatorsSatisfied groupWithInverse nodes Y.monsterRelators
    presentationSurjective :
      Presented.PresentedByY443Nodes groupWithInverse nodes
    pathShifts :
      All.JMDPathShiftCertificate groupWithInverse nodes
    construction : VN.VNaturalConstruction
    action :
      VOA.VOAGroupAction
        G (TM.GroupWithInverse.group groupWithInverse)
        (VN.VNaturalConstruction.Vnatural construction)

open PresentedY443VNaturalSource public

compileNodeWords :
  ∀ {G} (src : PresentedY443VNaturalSource G) →
  Pair.NodeWordCertificate
    (groupWithInverse src)
    (Source.uElement (groupWithInverse src) (nodes src))
    (Source.vElement (groupWithInverse src) (nodes src))
    (nodes src)
compileNodeWords src =
  All.Recover.actualNodeWordCertificate
    (groupWithInverse src) (nodes src)
    (relatorsHold src) (pathShifts src)

compileNodeGeneration :
  ∀ {G} (src : PresentedY443VNaturalSource G) →
  Pair.NodeGeneration (groupWithInverse src) (nodes src)
compileNodeGeneration src =
  Presented.nodeGenerationFromPresentedSyntax
    (groupWithInverse src) (nodes src) (presentationSurjective src)

compileSelectedWeld :
  ∀ {G} (src : PresentedY443VNaturalSource G) →
  Pair.Y443VNaturalPairWeld G
compileSelectedWeld src =
  record
    { Pair.groupWithInverse = groupWithInverse src
    ; Pair.construction = construction src
    ; Pair.voaAction = action src
    ; Pair.u = Source.uElement (groupWithInverse src) (nodes src)
    ; Pair.v = Source.vElement (groupWithInverse src) (nodes src)
    ; Pair.nodes = nodes src
    ; Pair.nodeWordCertificate = compileNodeWords src
    ; Pair.nodesGenerate = compileNodeGeneration src
    ; Pair.y443RelatorsHold = relatorsHold src
    }

wholeGroupTwoGenerated :
  ∀ {G} (src : PresentedY443VNaturalSource G) →
  (g : G) →
  Pair.RepresentedByPair
    (groupWithInverse src)
    (Source.uElement (groupWithInverse src) (nodes src))
    (Source.vElement (groupWithInverse src) (nodes src))
    g
wholeGroupTwoGenerated src =
  Pair.pairWordsSurjective
    (groupWithInverse src)
    (Source.uElement (groupWithInverse src) (nodes src))
    (Source.vElement (groupWithInverse src) (nodes src))
    (nodes src)
    (compileNodeWords src) (compileNodeGeneration src)

sameLiteralVNaturalActionWord :
  ∀ {G} (src : PresentedY443VNaturalSource G) →
  (g : G)
  (state : Pair.VNaturalState (compileSelectedWeld src)) →
  Pair.literalAction (compileSelectedWeld src)
    (Pair.evaluate (groupWithInverse src)
      (Source.uElement (groupWithInverse src) (nodes src))
      (Source.vElement (groupWithInverse src) (nodes src))
      (Pair.word (wholeGroupTwoGenerated src g))) state
  ≡
  Pair.literalAction (compileSelectedWeld src) g state
sameLiteralVNaturalActionWord src g state =
  Pair.cong (λ x → Pair.literalAction (compileSelectedWeld src) x state)
    (Pair.interpretation (wholeGroupTwoGenerated src g))
