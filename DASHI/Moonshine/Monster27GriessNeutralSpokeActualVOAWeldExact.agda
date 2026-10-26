module DASHI.Moonshine.Monster27GriessNeutralSpokeActualVOAWeldExact where

-- Explicitly reuse pre-existing FLM Griess unit proof owner and
-- the SAME Monster 27 parent/selected 3B literal VOA source.
--
-- External theorem: on Vnatural_2, (omega/2) is the Griess identity
-- for product u star v = u_(1)v. The literal mode source receipt is
-- deliberately NOT instantiated: source-written does not equal a
-- constructed Vnatural mode implementation or kernel verification.
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer using (ℤ; +_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Biology.MoonshineGriessAutomorphismClassificationExact as Griess
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Moonshine.Monster27VOAOnsiteCube369BridgeExact as Parent
import DASHI.Moonshine.MonsterGradedVOALiteralActionSameObjectBidiExact as Weld
import DASHI.Moonshine.MonsterGradedVOASelected3BSameElementBidiExact as Selected
import DASHI.Moonshine.VertexOperatorAlgebraCore as Core

actualVOA :
  ∀ {Monster K : Set} →
  Parent.Monster27VOAOnCubeSource Monster K →
  Core.VertexOperatorAlgebra
actualVOA source =
  Core.MoonshineVOABridge.voa
    (Weld.literalVOA (Selected.weld (Parent.selected3B source)))

ActualState :
  ∀ {Monster K : Set} →
  Parent.Monster27VOAOnCubeSource Monster K → Set
ActualState source =
  Core.GradedModule.Carrier
    (Core.VertexOperatorAlgebra.gradedModule (actualVOA source))

actualFirstMode :
  ∀ {Monster K : Set}
    (source : Parent.Monster27VOAOnCubeSource Monster K) →
    ActualState source → ActualState source → ActualState source
actualFirstMode source a b =
  Core.VertexOperatorData.mode
    (Core.VertexOperatorAlgebra.vertexData (actualVOA source))
    a (+ 1) b

record SameVOAGriessUnitSource
  {Monster K : Set}
  (source : Parent.Monster27VOAOnCubeSource Monster K) : Setω where
  field
    griess : Griess.UnitalCommutativeAlgebra
    -- An explicit comparison to the EXISTING selected literal Vnatural
    -- state space, not a second unrelated putative Griess algebra.
    embed : Griess.Carrier griess → ActualState source
    modeOneIsSameProduct :
      (u v : Griess.Carrier griess) →
      embed (Griess.multiply griess u v)
        ≡ actualFirstMode source (embed u) (embed v)
    -- Chosen nonzero representative of each of the 27 charge blocks.
    -- Graded eigencharge certification belongs to the existing
    -- source-owned Monster weight-two action, not to mere geometry.
    chargedRepresentative :
      Cube.Ternary27Point → Griess.Carrier griess
    Nonzero : ActualState source → Set
    representativeIsNonzero :
      (p : Cube.Ternary27Point) →
      Nonzero (embed (chargedRepresentative p))
open SameVOAGriessUnitSource public

-- Concrete exact source-matched VOA-mode identity, conditional on a
-- genuine same-object product witness. It applies to all 27 charges.
neutralToChargeFirstMode :
  ∀ {Monster K : Set}
  (source : Parent.Monster27VOAOnCubeSource Monster K)
  (receipt : SameVOAGriessUnitSource source)
  (p : Cube.Ternary27Point) →
  actualFirstMode source
    (embed receipt (chargedRepresentative receipt p))
    (embed receipt (Griess.unit (griess receipt)))
    ≡ embed receipt (chargedRepresentative receipt p)
neutralToChargeFirstMode source receipt p =
  trans
    (sym
      (modeOneIsSameProduct receipt
        (chargedRepresentative receipt p)
        (Griess.unit (griess receipt))))
    (cong (embed receipt)
      (Griess.rightIdentity (griess receipt)
        (chargedRepresentative receipt p)))

-- Exactly six cube-neighbour edges are incident to the centre.
-- On those, the genuine VOA Griess unit produces a nonzero
-- neutral-to-charge mode; no universal nonzero weight-two matrix
-- element on the other 48 edges is inferred.
