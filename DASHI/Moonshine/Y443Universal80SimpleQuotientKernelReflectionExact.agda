module DASHI.Moonshine.Y443Universal80SimpleQuotientKernelReflectionExact where

------------------------------------------------------------------------
-- SOURCE-EXACT NONABELIAN KERNEL REFLECTION FROM SIMPLE 80 QUOTIENT.
--
-- This replaces the infeasible plan to enumerate every equality in the
-- original selected G with the ordinary simple-group kernel argument.
--
-- The mathematical input is the ORIGINAL Ivanov/Bray theorem that the
-- true 80-relator quotient is the Monster, plus Monster simplicity;
-- NOT a generic assumption that the selected group has no extra
-- relations. Their honest source interpretation remains outstanding.
--
-- One selected generator must act nontrivially, and actual node words
-- must cover G for the resulting selected-group isomorphism.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
import DASHI.Moonshine.Y443Universal80RelatorCongruenceExact as U
import DASHI.Moonshine.Y443PresentedGroupNodeGenerationExact as Presented
import DASHI.Moonshine.Y443VNaturalPairGenerationExact as Pair
import DASHI.Moonshine.Y443CoxeterPresentationExact as Y
import DASHI.Moonshine.Y443JMDPowerFiveSixAlgebraExact as Algebra
import DASHI.Moonshine.TwistedModuleModularity as TM
import DASHI.Moonshine.Y443TwoGeneratorSameVOAActionExact as Actions
import DASHI.Moonshine.Y443JMDPresentedVNaturalCapstoneExact as JMD
import DASHI.Moonshine.VertexOperatorAlgebraCore as VOA
import DASHI.Moonshine.VNaturalOrbifoldConstruction as VN

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

-- For the universal *actual* 80-relator setoid group, normal subgroup
-- simplicity is equivalently a dichotomy for GROUP CONGRUENCES containing
-- the original 80 relations. This is NOT a statement of the C2 parity
-- theorem: perfectness alone does not imply this dichotomy.
record Original80SimpleCongruenceAuthority : Set₂ where
  field
    everyGroupCongruenceIsTrivialOrTotal :
      (C : U.AdmissibleCongruence) →
      ((∀ {x y} → U.R C x y → U._≈₈₀_ x y)
       ⊎
       (∀ x y → U.R C x y))
open Original80SimpleCongruenceAuthority public

module Selected
    {G : Set}
    (gi : TM.GroupWithInverse G)
    (nodes : Y.Node → G)
    (originalRelators :
      Pair.RelatorsSatisfied gi nodes Y.monsterRelators) where

  module I = U.Interpretation gi nodes originalRelators
  module A = Algebra.PowerAlgebra gi

  -- The actual selected word-evaluation kernel is an admissible
  -- congruence because original group operations are genuine and all
  -- original 80 relators hold under the selected node interpretation.
  originalSelectedKernel : U.AdmissibleCongruence
  originalSelectedKernel = record
    { U.AdmissibleCongruence.R =
        λ x y → I.eval x ≡ I.eval y
    ; U.AdmissibleCongruence.rRefl = λ x → refl
    ; U.AdmissibleCongruence.rSym = Algebra.sym
    ; U.AdmissibleCongruence.rTrans = Algebra.trans
    ; U.AdmissibleCongruence.rMul =
        Algebra.cong₂ (Pair.multiply gi)
    ; U.AdmissibleCongruence.rInv =
        Algebra.cong (Pair.inverse gi)
    ; U.AdmissibleCongruence.rAssoc =
        λ x y z → A.assoc (I.eval x) (I.eval y) (I.eval z)
    ; U.AdmissibleCongruence.rLeftId =
        λ x → A.leftId (I.eval x)
    ; U.AdmissibleCongruence.rRightId =
        λ x → A.rightId (I.eval x)
    ; U.AdmissibleCongruence.rLeftInverse =
        λ x → TM.GroupWithInverse.leftInverse gi (I.eval x)
    ; U.AdmissibleCongruence.rRightInverse =
        λ x → TM.GroupWithInverse.rightInverse gi (I.eval x)
    ; U.AdmissibleCongruence.rSourceRelator =
        λ w member → I.sound (U.sourceRelator w member)
    }

  -- A concrete selected node that is NOT the identity suffices.
  -- No all-elements kernel reflection premise is used.
  record ActualSelectedNontrivialNode : Set where
    field
      witnessNode : Y.Node
      witnessNonidentity :
        nodes witnessNode ≢ Pair.identity gi
  open ActualSelectedNontrivialNode public

  -- A single MOVED STATE of the actual typed selected group action
  -- proves the original witness is not the identity. This is much
  -- weaker than assuming faithful action or an all-word isomorphism.
  nonidentityNodeFromMovingState :
    ∀ {S : Set} →
    (action : Actions.ActualGroupAction {G} {S} gi) →
    (n : Y.Node) (state : S) →
    Actions.act action (nodes n) state ≢ state →
    ActualSelectedNontrivialNode
  nonidentityNodeFromMovingState action n state moves = record
    { witnessNode = n
    ; witnessNonidentity = λ eq →
        moves (Algebra.trans
          (Algebra.cong (λ g → Actions.act action g state) eq)
          (Actions.actsIdentity action state))
    }

  simpleQuotientAndOneNonidentityNodeReflectsAllWords :
    Original80SimpleCongruenceAuthority →
    ActualSelectedNontrivialNode →
    ∀ x y → I.eval x ≡ I.eval y → U._≈₈₀_ x y
  simpleQuotientAndOneNonidentityNodeReflectsAllWords
    simple selected x y eq
    with everyGroupCongruenceIsTrivialOrTotal simple originalSelectedKernel
  ... | inj₁ minimal = minimal eq
  ... | inj₂ total =
    absurd (witnessNonidentity selected
      (total (Presented.generator (witnessNode selected))
             Presented.empty))
    where
    absurd : ⊥ → U._≈₈₀_ x y
    absurd ()

  actualKernelReflectionFromPublishedSimplicity :
    Original80SimpleCongruenceAuthority →
    ActualSelectedNontrivialNode →
    I.NoExtraSelectedRelations
  actualKernelReflectionFromPublishedSimplicity simple selected =
    record
      { I.NoExtraSelectedRelations.reflectsEquality =
          simpleQuotientAndOneNonidentityNodeReflectsAllWords
            simple selected
      }


  -- The subgroup/image actually generated by the 12 selected nodes can
  -- be defined as a setoid group on original words, modulo equality
  -- of their selected evaluations. No surjectivity onto all G required.
  selectedImageSetoidGroup : U.SetoidGroup
  selectedImageSetoidGroup = record
    { U.SetoidGroup.Carrier = U.Expr
    ; U.SetoidGroup.Equivalent = U.R originalSelectedKernel
    ; U.SetoidGroup.unit = Presented.empty
    ; U.SetoidGroup.product = Presented.multiply
    ; U.SetoidGroup.inverse = Presented.inverse
    ; U.SetoidGroup.reflexive =
        U.rRefl originalSelectedKernel
    ; U.SetoidGroup.symmetric =
        U.rSym originalSelectedKernel
    ; U.SetoidGroup.transitive =
        U.rTrans originalSelectedKernel
    ; U.SetoidGroup.productCongruent =
        U.rMul originalSelectedKernel
    ; U.SetoidGroup.inverseCongruent =
        U.rInv originalSelectedKernel
    ; U.SetoidGroup.associative =
        U.rAssoc originalSelectedKernel
    ; U.SetoidGroup.leftUnit =
        U.rLeftId originalSelectedKernel
    ; U.SetoidGroup.rightUnit =
        U.rRightId originalSelectedKernel
    ; U.SetoidGroup.leftInverse =
        U.rLeftInverse originalSelectedKernel
    ; U.SetoidGroup.rightInverse =
        U.rRightInverse originalSelectedKernel
    }

  -- The selected-image word relation is *exactly* the original
  -- 80-relator quotient relation once the published simple quotient
  -- and one nonidentity selected image are supplied. In particular,
  -- selected-word generation of ALL of G is not necessary here.
  simpleSourceIdentifiesOriginalAndImageSetoids :
    Original80SimpleCongruenceAuthority →
    ActualSelectedNontrivialNode →
    (x y : U.Expr) →
    (U._≈₈₀_ x y → U.R originalSelectedKernel x y)
      ×
    (U.R originalSelectedKernel x y → U._≈₈₀_ x y)
  simpleSourceIdentifiesOriginalAndImageSetoids simple selected x y =
    (λ p → I.sound p) ,
    (simpleQuotientAndOneNonidentityNodeReflectsAllWords simple selected x y)

  module WithOriginalSources
    (simple : Original80SimpleCongruenceAuthority)
    (selected : ActualSelectedNontrivialNode)
    (generated : Presented.PresentedByY443Nodes gi nodes) where

    selectedKernel : I.NoExtraSelectedRelations
    selectedKernel = actualKernelReflectionFromPublishedSimplicity
      simple selected

    module Iso = I.SelectedEquivalence generated selectedKernel

    -- The actual original selected group is now equivalent, in the
    -- correct setoid-group sense, to the universal 80-relator quotient.
    selectedToAfterFrom :
      (g : G) → I.eval (Iso.fromSelected g) ≡ g
    selectedToAfterFrom = Iso.toAfterFrom

    presentedFromAfterTo :
      (w : U.Expr) →
      U._≈₈₀_ (Iso.fromSelected (I.eval w)) w
    presentedFromAfterTo = Iso.fromAfterTo


------------------------------------------------------------------------
-- DIRECT REUSE OF THE EXISTING ORIGINAL SELECTED JMD/VNATURAL OWNER.
-- No parallel choice of G, no independent node map, and no rebuilt
-- signed-word generation source. The three genuinely uninhabited
-- sources (actual JMD selection, historical simplicity, moved state)
-- remain visible.
------------------------------------------------------------------------

module OriginalSelectedJMDSource
    {G : Set}
    (source : JMD.PresentedY443VNaturalSource G) where

  module Real = Selected
    (JMD.groupWithInverse source)
    (JMD.nodes source)
    (JMD.relatorsHold source)


  -- This is THE LITERAL source selected group action on the actual
  -- selected Vnatural carrier. The older VOAGroupAction has only a
  -- Set-valued identity-law field, so we request just the single
  -- genuine identity action equation needed at the moved state.
  SelectedState : Set
  SelectedState =
    VOA.GradedModule.Carrier
      (VOA.VertexOperatorAlgebra.gradedModule
        (VN.VNaturalConstruction.Vnatural (JMD.construction source)))

  literalSelectedAction : G → SelectedState → SelectedState
  literalSelectedAction =
    VOA.VOAGroupAction.act (JMD.action source)

  oneOriginalMovedStateImpliesNontrivialNode :
    (n : Y.Node) (state : SelectedState) →
    literalSelectedAction
      (Pair.identity (JMD.groupWithInverse source)) state ≡ state →
    literalSelectedAction (JMD.nodes source n) state ≢ state →
    Real.ActualSelectedNontrivialNode
  oneOriginalMovedStateImpliesNontrivialNode n state identityAt moves =
    record
      { Real.ActualSelectedNontrivialNode.witnessNode = n
      ; Real.ActualSelectedNontrivialNode.witnessNonidentity =
          λ equality →
            moves (Algebra.trans
              (Algebra.cong
                (λ g → literalSelectedAction g state) equality)
              identityAt)
      }

  module FromHistoricalAndMovedState
    (simple : Original80SimpleCongruenceAuthority)
    (moved : Real.ActualSelectedNontrivialNode) where

    originalKernelReflection : ∀ x y →
      Real.I.eval x ≡ Real.I.eval y → U._≈₈₀_ x y
    originalKernelReflection =
      Real.simpleQuotientAndOneNonidentityNodeReflectsAllWords
        simple moved

    module SameJMD = Real.WithOriginalSources
      simple moved (JMD.presentationSurjective source)

    actualSelectedToAfterFrom :
      (g : G) →
      Real.I.eval (SameJMD.Iso.fromSelected g) ≡ g
    actualSelectedToAfterFrom = SameJMD.selectedToAfterFrom

    actualPresentedFromAfterTo :
      (w : U.Expr) →
      U._≈₈₀_
        (SameJMD.Iso.fromSelected (Real.I.eval w)) w
    actualPresentedFromAfterTo = SameJMD.presentedFromAfterTo
