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
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
import DASHI.Moonshine.Y443Universal80RelatorCongruenceExact as U
import DASHI.Moonshine.Y443PresentedGroupNodeGenerationExact as Presented
import DASHI.Moonshine.Y443VNaturalPairGenerationExact as Pair
import DASHI.Moonshine.Y443CoxeterPresentationExact as Y
import DASHI.Moonshine.Y443JMDPowerFiveSixAlgebraExact as Algebra
import DASHI.Moonshine.TwistedModuleModularity as TM

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

-- For the universal *actual* 80-relator setoid group, normal subgroup
-- simplicity is equivalently a dichotomy for GROUP CONGRUENCES containing
-- the original 80 relations. This is NOT a statement of the C2 parity
-- theorem: perfectness alone does not imply this dichotomy.
record Original80SimpleCongruenceAuthority : Set₁ where
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

  module WithOriginalSources
    (simple : Original80SimpleCongruenceAuthority)
    (selected : ActualSelectedNontrivialNode)
    (generated : Presented.PresentedByY443Nodes gi nodes) where

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
