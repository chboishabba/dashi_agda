module DASHI.Moonshine.Y443Relator72IndexedBidiExact where

------------------------------------------------------------------------
-- Concrete relator-label partition and word preservation.
-- 80 labelled relation indices <-> original word list, in the EXACT
-- order of Y443CoxeterPresentationExact.
--
-- Under the canonical graph arm-swap, the relator-index classifier uses:
-- 72 core = ALL 55 nonedge + eight exchanged-arm generator squares
--           + eight exchanged-arm edge powers + central-vertex square
-- 8 residual = three short-arm squares + three short-arm edge powers
--               + spider + Ivanov central quotient.
--
-- A 72-to-(8 x 9) phase chart remains a distinct semantic map:
-- this theorem does not manufacture a C3/369-equivariant bijection.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.List using (List; []; _∷_)
import DASHI.Moonshine.Y443CoxeterPresentationExact as Y
import DASHI.Moonshine.Y443ArmSwapOrbitMaxCutExact as Orbit
import DASHI.Foundations.BalancedTernaryAntipodal369OrbitHierarchyExact as Ternary

data RelatorTag : Set where
  nodeSquare : Y.Node → RelatorTag
  pairPower : Y.Pair → RelatorTag
  spider : RelatorTag
  centralQuotient : RelatorTag

relatorWord : RelatorTag → Y.Word
relatorWord (nodeSquare n) = Y.square n
relatorWord (pairPower p) = Y.pairRelator p
relatorWord spider = Y.spiderRelator
relatorWord centralQuotient = Y.centralInvolutionRelator

coxeterTags : List RelatorTag
coxeterTags =
  Y._++_ (Y.map nodeSquare Y.nodes) (Y.map pairPower Y.pairs)

fullTags : List RelatorTag
fullTags = Y._++_ coxeterTags (spider ∷ centralQuotient ∷ [])

tagCount : Y.length fullTags ≡ 80
tagCount = refl

-- This ties the new partition back to the original relator WORDS.
allTagsRecoverOriginal80Words :
  Y.map relatorWord fullTags ≡ Y.monsterRelators
allTagsRecoverOriginal80Words = refl

core : RelatorTag → Bool
core (nodeSquare n) =
  Orbit.orB (Orbit.isCentralNode n) (Orbit.isMovingNode n)
core (pairPower p) =
  Orbit.orB
    (Orbit.notB (Y.adjacent (Y.first p) (Y.second p)))
    (Orbit.notB (Orbit.isFixedPair p))
core spider = false
core centralQuotient = false

residual : RelatorTag → Bool
residual tag = Orbit.notB (core tag)

count : (RelatorTag → Bool) → List RelatorTag → Nat
count predicate [] = 0
count predicate (x ∷ xs) =
  Orbit.ind (predicate x) + count predicate xs

coxeterCoreCount : count core coxeterTags ≡ 72
coxeterCoreCount = refl

coxeterResidualCount : count residual coxeterTags ≡ 6
coxeterResidualCount = refl

fullCoreCount : count core fullTags ≡ 72
fullCoreCount = refl

fullResidualCount : count residual fullTags ≡ 8
fullResidualCount = refl

coreThenResidualReconstitutes80 :
  count core fullTags + count residual fullTags ≡ 80
coreThenResidualReconstitutes80 = refl

-- A C3/369 chart would need a proof-relevant mapping of *these same*
-- tagged relators, not a chart of an arbitrary Fin 72.
record EightByNineRelatorPhaseChart (Mode8 Mode9 : Set) : Set₁ where
  field
    Mode8By9 : Set
    fineChart : RelatorTag → Mode8By9
    recognisesCore : RelatorTag → Set
    phaseTransportPreservesRelatorFamily : Set

-- The existing ternary 9/27 symmetry has a unique fixed centre;
-- the actual Y443 arm-swap has THREE fixed edge-relators and SEVEN fixed
-- nonedge-relators, so quotient counts cannot be identified by notation.

nineHasFiveClasses :
  Ternary.quotientOrbitCount Ternary.rank2 ≡ 5
nineHasFiveClasses = Ternary.rank2CountIsFive

twentySevenHasFourteenClasses :
  Ternary.quotientOrbitCount Ternary.rank3 ≡ 14
twentySevenHasFourteenClasses = Ternary.rank3CountIsFourteen

y443EdgeHasSevenClasses : Orbit.edgeOrbitCount ≡ 7
y443EdgeHasSevenClasses = Orbit.edgeHasSevenOrbitClasses

y443NonedgeHasThirtyOneClasses : Orbit.nonedgeOrbitCount ≡ 31
y443NonedgeHasThirtyOneClasses = Orbit.nonedgeHasThirtyOneOrbitClasses
