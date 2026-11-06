module DASHI.Moonshine.Y443MonsterGradedLiteralSameObjectCapstoneExact where

------------------------------------------------------------------------
-- NO PARALLEL VOA ACTION: source-exact same-object bridge
--
-- Reuses MonsterGradedVOALiteralActionSameObjectBidiExact, whose
-- MoonshineVOABridge shares the exact graded Monster character
-- authority and literal state action.
--
-- The following two equality witnesses explicitly identify the
-- chosen group law and VOA with the already-selected actual
-- VNaturalConstruction. Refl transport reuses the ORIGINAL
-- VOAGroupAction, not a freshly declared "compatible" action.
--
-- The JMD power/path/presentation compiler then yields two-generator
-- transport on the SAME selected VOA state carrier.
--
-- Full Aut_VOA(Vnatural)=Monster requires separate faithfulness,
-- automorphism surjectivity and source representation recognition;
-- the chosen action alone is NOT a full-aut-group theorem.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Moonshine.GradedRepresentation as GR
import DASHI.Moonshine.TwistedModuleModularity as TM
import DASHI.Moonshine.VertexOperatorAlgebraCore as VOA
import DASHI.Moonshine.VNaturalOrbifoldConstruction as VN
import DASHI.Moonshine.MonsterGradedVOALiteralActionSameObjectBidiExact as Same
import DASHI.Moonshine.MonsterGradedVOABridgeExact as Legacy
import DASHI.Moonshine.GradedVertexOperatorAlgebraBoundary as Graded
import DASHI.Moonshine.VertexOperatorAlgebraLinearActionReceiptExact as Linear
import DASHI.Moonshine.Y443CoxeterPresentationExact as Y
import DASHI.Moonshine.Y443VNaturalPairGenerationExact as Pair
import DASHI.Moonshine.Y443JMDAllTwelveNodeWordCompilerExact as Paths
import DASHI.Moonshine.Y443PresentedGroupNodeGenerationExact as Presented
import DASHI.Moonshine.Y443JMDPresentedVNaturalCapstoneExact as Cap
import DASHI.Moonshine.Y443JMDSourceWordInstantiationExact as JMD

transportVOAGroupAction :
  ∀ {G : Set}
    {g h : GR.Group G}
    {v w : VOA.VertexOperatorAlgebra} →
  g ≡ h → v ≡ w →
  VOA.VOAGroupAction G g v →
  VOA.VOAGroupAction G h w
transportVOAGroupAction refl refl a = a

record SelectedMonsterLiteralY443Source
  (Monster K : Set) : Setω where
  field
    gradedLiteral : Same.MonsterGradedVOALiteralActionWeld Monster K

    gi : TM.GroupWithInverse Monster
    construction : VN.VNaturalConstruction

    -- Selected group is literally the SAME law as the graded authority.
    groupAgrees :
      Graded.group (Legacy.voaAction (Same.gradedAuthority gradedLiteral))
      ≡ TM.GroupWithInverse.group gi

    -- Selected Vnatural orbifold is literally the SAME VOA as the graded
    -- action's literal state carrier.
    VNaturalAgrees :
      Same.LiteralVOA gradedLiteral
      ≡ VN.VNaturalConstruction.Vnatural construction

    -- The source has a concrete presentation and its exact relators.
    nodes : Y.Node → Monster
    relators :
      Pair.RelatorsSatisfied gi nodes Y.monsterRelators
    sourcePresented :
      Presented.PresentedByY443Nodes gi nodes

    -- Stronger optional linearity structure reuses the ACTUAL
    -- legacy literal action. Not another vector-space instance.
    actionIsLinear :
      Linear.VOAGroupActionLinearReceipt
        (Graded.group (Legacy.voaAction (Same.gradedAuthority gradedLiteral)))
        (Same.LiteralVOA gradedLiteral)
        (VOA.monsterAction (Same.literalVOA gradedLiteral))

open SelectedMonsterLiteralY443Source public

actualActionTransported :
  ∀ {Monster K}
  (source : SelectedMonsterLiteralY443Source Monster K) →
  VOA.VOAGroupAction Monster
    (TM.GroupWithInverse.group (gi source))
    (VN.VNaturalConstruction.Vnatural (construction source))
actualActionTransported source =
  transportVOAGroupAction
    (groupAgrees source) (VNaturalAgrees source)
    (VOA.monsterAction (Same.literalVOA (gradedLiteral source)))

actualGradedMonsterCapstone :
  ∀ {Monster K}
  (source : SelectedMonsterLiteralY443Source Monster K) →
  Cap.PresentedY443VNaturalSource Monster
actualGradedMonsterCapstone source =
  record
    { Cap.groupWithInverse = gi source
    ; Cap.nodes = nodes source
    ; Cap.relatorsHold = relators source
    ; Cap.presentationSurjective = sourcePresented source
    ; Cap.construction = construction source
    ; Cap.action = actualActionTransported source
    }

sameActualGradedMonsterActionTwoGenerated :
  ∀ {Monster K}
  (source : SelectedMonsterLiteralY443Source Monster K) →
  (g : Monster) →
  Pair.RepresentedByPair
    (gi source)
    (JMD.uElement
      (gi source) (nodes source))
    (JMD.vElement
      (gi source) (nodes source))
    g
sameActualGradedMonsterActionTwoGenerated source =
  Cap.wholeGroupTwoGenerated (actualGradedMonsterCapstone source)
