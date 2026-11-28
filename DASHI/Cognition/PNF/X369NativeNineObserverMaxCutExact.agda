module DASHI.Cognition.PNF.X369NativeNineObserverMaxCutExact where

-- SOURCE-OWNED FULL NINE-TRIT GEOMETRY. Six signed scalar coordinates are
-- only a possible downstream consumer chart, not the hyperfabric.
-- Attribution: original Leech-LILA Anatolii Kornienko; DASHI extension.
-- Kernel checking intentionally deferred. No postulates/holes/CI.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
import DASHI.Foundations.SSPTritCarrier as T
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as H
import DASHI.Foundations.Base369NineCoordinateAggregateBridgeExact as N
import DASHI.Cognition.PNF.X369InputIndexedFutureConsumerExact as F

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

Full : Set
Full = H.TernaryHyperformalPoint

Interaction : Set
Interaction = H.Ternary27Point

Appraisals : Set
Appraisals = H.AppraisalFibrePoint

-- Full nine-trit BIDI is already provided by the native source.
fullToNine : Full → N.NineTrits
fullToNine = H.fabricToNineTrits

nineToFull : N.NineTrits → Full
nineToFull = H.nineTritsToFabric

nineBidiLeft : (x : Full) → nineToFull (fullToNine x) ≡ x
nineBidiLeft = H.fabricNineRoundTrip

nineBidiRight : (x : N.NineTrits) → fullToNine (nineToFull x) ≡ x
nineBidiRight = H.nineFabricRoundTrip

-- An exact product observer includes BOTH appraisal cubes.
fullProduct : Full → Interaction × Appraisals
fullProduct x = H.projectInteractionVoxel x , H.projectAppraisalFibre x

rebuild : Interaction × Appraisals → Full
rebuild (i , a) = H.rebuildOverInteraction i a

productBidiLeft : (x : Full) → rebuild (fullProduct x) ≡ x
productBidiLeft (H.ternaryHyperformalPoint i a b) = refl

productBidiRight : (x : Interaction × Appraisals) →
  fullProduct (rebuild x) ≡ x
productBidiRight (i , H.appraisalFibrePoint a b) = refl

-- Genuine SAME-INTERACTION fibre collision, rather than a cardinality
-- argument. The consumer observing appraisal A distinguishes the pair.
p0 p1 : Full
p0 = H.ternaryHyperformalPoint H.origin H.origin H.origin
p1 = H.ternaryHyperformalPoint H.origin
  (H.ternary27Point T.sspPosOne T.sspZero T.sspZero) H.origin

sameInteraction :
  H.projectInteractionVoxel p0 ≡ H.projectInteractionVoxel p1
sameInteraction = refl

observeAppraisalA : Full → Interaction
observeAppraisalA = H.appraisalAVoxel

differentTrit : T.sspZero ≡ T.sspPosOne → ⊥
differentTrit ()

differentAppraisal :
  observeAppraisalA p0 ≡ observeAppraisalA p1 → ⊥
differentAppraisal eq = differentTrit (cong H.x eq)

-- No function of the interaction voxel alone can reproduce this original
-- appraisal consumer globally. This is an exact counterexample to making
-- "interaction projection" a universal sufficient consumer.
noInteractionOnlyAppraisalReader :
  (read : Interaction → Interaction) →
  ((x : Full) → read (H.projectInteractionVoxel x) ≡ observeAppraisalA x) →
  ⊥
noInteractionOnlyAppraisalReader read faithful =
  differentAppraisal
    (trans (sym (faithful p0))
      (trans (cong read sameInteraction) (faithful p1)))

-- Neither the 6-channel action nor the full 9-trit universe determines
-- which histories, physical-time fibres or consumer versions descend.
-- When a candidate chart is supplied, these are the exact and sufficient
-- one-step constructor obligations for ALL finite future words.
module SourceIndexedDescent
  {Input Code Output : Set}
  (fineStep : Input → Full → Full)
  (fineObserve : Input → Full → Output)
  (chart : Full → Code)
  (codedStep : Input → Code → Code)
  (codedObserve : Input → Code → Output)
  (commute : (u : Input) (x : Full) →
    chart (fineStep u x) ≡ codedStep u (chart x))
  (observeWeld : (u : Input) (x : Full) →
    fineObserve u x ≡ codedObserve u (chart x)) where

  observationFibreStable : (u : Input) (x y : Full) →
    chart x ≡ chart y → fineObserve u x ≡ fineObserve u y
  observationFibreStable u x y same =
    trans (observeWeld u x)
      (trans (cong (codedObserve u) same)
        (sym (observeWeld u y)))

  transitionFibreStable : (u : Input) (x y : Full) →
    chart x ≡ chart y →
    chart (fineStep u x) ≡ chart (fineStep u y)
  transitionFibreStable u x y same =
    trans (commute u x)
      (trans (cong (codedStep u) same)
        (sym (commute u y)))

  allFutureWordsDescend : (inputs : List Input) (x y : Full) →
    chart x ≡ chart y →
    F.trace fineStep fineObserve inputs x ≡
    F.trace fineStep fineObserve inputs y
  allFutureWordsDescend inputs x y same =
    F.inputIndexedTraceDescent fineStep fineObserve chart
      observationFibreStable transitionFibreStable inputs x y same

-- Geometry witnesses already owned elsewhere:
-- GovernedIndexedResidualCubeExact (all six exact faces; residual != equality)
-- IndexedCubeHyperfibreExact (typed path/resolution and local chart)
-- IndexedAffineCornerAppraisal5832Exact (8*729 address BIDI)
-- HyperfabricPunctured27Projective13OrientationExact (13*2 + origin)
-- Base369ZeroFibre (6 x_3 9 = 18; six visible-zero hidden states).
-- No equality of these distinct carriers is inferred from equal numerals.
