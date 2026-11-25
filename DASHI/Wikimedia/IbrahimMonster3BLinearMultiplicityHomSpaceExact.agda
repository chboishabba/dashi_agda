module DASHI.Wikimedia.IbrahimMonster3BLinearMultiplicityHomSpaceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import DASHI.Moonshine.Monster3BCentralCharacterInertiaExact as Inertia

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Geometry.HilbertLorentzForcing as Linear
import DASHI.Moonshine.Monster3BActualLinearWeightFrameExact as Frame
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Wikimedia.IbrahimMonster3BLinearZetaSectorRestrictionExact as Zeta
import DASHI.Moonshine.Monster3BNormalizerCocycleCancellationExact as Cocycle
import DASHI.Moonshine.Monster3BModelStoneVonNeumannRecognitionExact as FiniteModel
import DASHI.Wikimedia.IbrahimMonster3BMultiplicityBasisLinearWrongTypeCorrectionExact as WrongType
import DASHI.Wikimedia.IbrahimMonster3BPhaseResolvedCharacterTwelveSeventyEightWeldExact as Character
import DASHI.Wikimedia.IbrahimMonster3BSuzukiNinetyPermutationCharacterNoGoExact as NoGo

------------------------------------------------------------------------
-- ACTUAL LINEAR MULTIPLICITY HOM SPACE
--
-- Canonical same-object target from the Monster 3B roadmap:
--
--   S_zeta = Hom_E(H_zeta , W_zeta)
--
-- together with a proof-bearing evaluation isomorphism
--
--   H_zeta tensor S_zeta  <->  W_zeta
--
-- at the LINEAR representation level.
--
-- This is deliberately distinct from the finite model
--
--   X6 x Fin 90 <-> ZetaModelBasis,
--
-- which is an isomorphism of basis labels and is useful for the finite Weyl
-- model but does not construct the ninety-dimensional multiplicity vector
-- space or its inertia action.
--
-- The projective inertia algebra is not reopened here.  The existing
-- Monster3BNormalizerCocycleCancellationExact owner already proves that a
-- projective Heisenberg action and inverse-projective multiplicity action
-- cancel to an honest tensor action.  This owner only requires the ACTUAL
-- same-object instantiation of that generic theorem.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Attribution / source roles.
------------------------------------------------------------------------

barracloughWilson : Attribution.AttributedSource
barracloughWilson = Attribution.mkDOISource
  "R. W. Barraclough; R. A. Wilson"
  "The Character Table of a Maximal Subgroup of the Monster"
  "LMS Journal of Computation and Mathematics 10, 161-175"
  "2007"
  "10.1112/S1461157000001352"
  "https://doi.org/10.1112/S1461157000001352"
  Attribution.academicArticleSource
  "primary source for the inertia-group character construction and the source-paid 12+78 multiplicity character; not a supplied linear Hom-space intertwiner"
  Attribution.publicAttribution

terras : Attribution.AttributedSource
terras = Attribution.mkDOISource
  "Audrey Terras"
  "Fourier Analysis on Finite Groups and Applications"
  "Cambridge University Press"
  "1999"
  "10.1017/CBO9780511626265"
  "https://doi.org/10.1017/CBO9780511626265"
  Attribution.academicArticleSource
  "finite-group Fourier/representation calibration for the Heisenberg evaluation and multiplicity-space viewpoint"
  Attribution.publicAttribution

serre : Attribution.AttributedSource
serre = Attribution.mkDOISource
  "Jean-Pierre Serre"
  "Linear Representations of Finite Groups"
  "Springer"
  "1977"
  "10.1007/978-1-4684-9458-7"
  "https://doi.org/10.1007/978-1-4684-9458-7"
  Attribution.academicArticleSource
  "representation-theory calibration for Hom spaces, tensor representations, projective lifts and character decomposition"
  Attribution.publicAttribution

barracloughWilsonAttribution = Snowball.canonicalSourceRoleSnowballReceipt barracloughWilson
terrasAttribution = Snowball.canonicalSourceRoleSnowballReceipt terras
serreAttribution = Snowball.canonicalSourceRoleSnowballReceipt serre

------------------------------------------------------------------------
-- 2. Proof-bearing same-object contract.
------------------------------------------------------------------------

-- Historical pure-pair API retained for existing consumers. It cannot be
-- inhabited as an evaluation equivalence of arbitrary linear tensors.
-- Use ActualLinearWeightHomSpace below for the full-vector endpoint.
record ActualLinearMultiplicityHomSpace : Set₁ where
  field
    HeisenbergCarrier : Set
    ChosenZetaCarrier : Set
    EquivariantMap : Set

    -- The same actual linear multiplicity representation identified in the
    -- WrongType correction.  Its vector carrier is the Hom-space carrier,
    -- modulo the explicit two-sided identification below rather than by fiat.
    sameObjectLinearRepresentation : WrongType.LinearMultiplicityRepresentation

    homToMultiplicity :
      EquivariantMap →
      Linear.Vector (WrongType.linearCarrier sameObjectLinearRepresentation)
    multiplicityToHom :
      Linear.Vector (WrongType.linearCarrier sameObjectLinearRepresentation) →
      EquivariantMap

    multiplicityAfterHom :
      (f : EquivariantMap) →
      multiplicityToHom (homToMultiplicity f) ≡ f
    homAfterMultiplicity :
      (s : Linear.Vector (WrongType.linearCarrier sameObjectLinearRepresentation)) →
      homToMultiplicity (multiplicityToHom s) ≡ s

    -- Actual evaluation/recovery, mirroring the finite-model constructive
    -- isomorphism but on the linear same-object carriers.
    evaluationMap :
      HeisenbergCarrier × EquivariantMap → ChosenZetaCarrier
    evaluationInverse :
      ChosenZetaCarrier → HeisenbergCarrier × EquivariantMap

    inverseAfterEvaluation :
      (tensor : HeisenbergCarrier × EquivariantMap) →
      evaluationInverse (evaluationMap tensor) ≡ tensor
    evaluationAfterInverse :
      (state : ChosenZetaCarrier) →
      evaluationMap (evaluationInverse state) ≡ state

    -- Same-object projective inertia instantiation.  The generic cancellation
    -- theorem already exists; these equalities pin its multiplicity and tensor
    -- carriers to this actual Hom-space/evaluation surface.
    cocycleCompensatedAction : Cocycle.CocycleCompensatedTensorAction

    cocycleMultiplicityIsSameLinearCarrier :
      Cocycle.Multiplicity cocycleCompensatedAction
      ≡ Linear.Vector (WrongType.linearCarrier sameObjectLinearRepresentation)

    cocycleTensorIsChosenZetaCarrier :
      Cocycle.Tensor cocycleCompensatedAction ≡ ChosenZetaCarrier

    sourcePaidCharacterOnSameMultiplicity : Set
    evaluationIsLinearIntertwiner : Set

open ActualLinearMultiplicityHomSpace public

------------------------------------------------------------------------
-- Full linear successor. The phase frame is on the SAME existing literal
-- zeta restriction and the SAME multiplicity linear carrier. The two
-- coordinate inverses are derived by Frame, not fields asserting an inverse
-- for Cartesian pairs. Actual representation and character inputs remain
-- proof-bearing source obligations.
------------------------------------------------------------------------

-- A Hom is an actual map with the linear and intertwining equations, not
-- an arbitrary Set identified by a dimension or basis label.
record EquivariantLinearMap
    (H W : Linear.HilbertLift) (E : Set)
    (scalarMap : Linear.Scalar H → Linear.Scalar W)
    (actH : E → Linear.Vector H → Linear.Vector H)
    (actW : E → Linear.Vector W → Linear.Vector W) : Set where
  field
    applyHom : Linear.Vector H → Linear.Vector W
    homZero : applyHom (Linear.zero H) ≡ Linear.zero W
    homAdd : ∀ u v →
      applyHom (Linear._+_ H u v) ≡ Linear._+_ W (applyHom u) (applyHom v)
    homScale : ∀ a v →
      applyHom (Linear._·_ H a v) ≡ Linear._·_ W (scalarMap a) (applyHom v)
    homEquivariance : ∀ g v →
      actW g (applyHom v) ≡ applyHom (actH g v)

open EquivariantLinearMap public

record ActualLinearWeightHomSpace : Set₁ where
  field
    literalSource : Zeta.LiteralLinearNormalizerSource
    literalLinearZeta : Zeta.LiteralLinearPhaseRestriction literalSource Inertia.phaseZeta
    weightFrame : Frame.ActualLinearWeightFrame
    frameIsLiteralZeta : Frame.sector weightFrame ≡ Zeta.phaseLinearCarrier literalLinearZeta
    multiplicityRepresentation : WrongType.LinearMultiplicityRepresentation
    vacuumIsMultiplicityCarrier :
      Frame.vacuum weightFrame ≡ WrongType.linearCarrier multiplicityRepresentation

    heisenbergCarrier : Linear.HilbertLift
    heisenbergScalarToSector :
      Linear.Scalar heisenbergCarrier → Linear.Scalar (Frame.sector weightFrame)
    HeisenbergBasis : H.X6 → Linear.Vector heisenbergCarrier
    vacuumPosition : H.X6
    E : Set
    actHeisenberg : E → Linear.Vector heisenbergCarrier → Linear.Vector heisenbergCarrier
    extraspecialToInertia : E →
      Inertia.CentralInertia (Zeta.literalNormalizerAction literalSource)

  -- Derive the target E action from the SAME literal phase restriction.
  actSector : E → Linear.Vector (Frame.sector weightFrame) →
    Linear.Vector (Frame.sector weightFrame)
  actSector g w =
    subst Linear.Vector (sym frameIsLiteralZeta)
      (Zeta.restrictInertia literalLinearZeta (extraspecialToInertia g)
        (subst Linear.Vector frameIsLiteralZeta w))

  EquivariantHom : Set
  EquivariantHom =
    EquivariantLinearMap heisenbergCarrier (Frame.sector weightFrame) E
      heisenbergScalarToSector actHeisenberg actSector

  evalHom : EquivariantHom → Linear.Vector heisenbergCarrier →
    Linear.Vector (Frame.sector weightFrame)
  evalHom = applyHom

  homToVacuum : EquivariantHom → Linear.Vector (Frame.vacuum weightFrame)
  homToVacuum f =
    Frame.recoverWeight weightFrame vacuumPosition
      (evalHom f (HeisenbergBasis vacuumPosition))

  field
    -- Lean MonsterVacuumHomEquivalence derives this constructor and its
    -- inverse from separating Weyl laws. Agda still needs actual inhabitants.
    vacuumToHom : Linear.Vector (Frame.vacuum weightFrame) → EquivariantHom
    vacuumAfterHom : ∀ f → vacuumToHom (homToVacuum f) ≡ f
    homAfterVacuum : ∀ u → homToVacuum (vacuumToHom u) ≡ u
    evalHomOnBasis : ∀ f x → evalHom f (HeisenbergBasis x) ≡
      Frame.includeWeight weightFrame x (homToVacuum f)

    -- Equality of functions alone is not trace authentication. The source
    -- compiler must prove that this trace is the trace of the actual action.
    traceOfMultiplicityAction :
      Linear.Group (WrongType.linearAction multiplicityRepresentation) →
      Linear.Scalar (WrongType.linearCarrier multiplicityRepresentation)
    selectedSourceCharacter :
      Linear.Group (WrongType.linearAction multiplicityRepresentation) →
      Linear.Scalar (WrongType.linearCarrier multiplicityRepresentation)
    sameCharacter : ∀ g → traceOfMultiplicityAction g ≡ selectedSourceCharacter g

open ActualLinearWeightHomSpace public

------------------------------------------------------------------------
-- 3. Existing finite-model theorem is retained as a donor, not promoted.
------------------------------------------------------------------------

finiteModelEvaluation : FiniteModel.FiniteEvaluationIsomorphism
finiteModelEvaluation = FiniteModel.canonicalFiniteEvaluationIsomorphism

------------------------------------------------------------------------
-- 4. WrongType / non-promotion firewalls.
------------------------------------------------------------------------

data CharacterCreatesHomEvaluation : Set where
data FiniteBasisEvaluationCreatesLinearHomEvaluation : Set where
data DimensionNinetyCreatesHomSpace : Set where
data CocycleCancellationCreatesActualCocycleLift : Set where
data NoPermutationCreatesLinearIntertwiner : Set where
data QidCreatesHomSpace : Set where
data DeweyCreatesHomSpace : Set where
data OeisCreatesHomSpace : Set where

characterDoesNotCreateHomEvaluation : CharacterCreatesHomEvaluation → ⊥
characterDoesNotCreateHomEvaluation ()

finiteBasisEvaluationDoesNotCreateLinearHomEvaluation :
  FiniteBasisEvaluationCreatesLinearHomEvaluation → ⊥
finiteBasisEvaluationDoesNotCreateLinearHomEvaluation ()

dimensionDoesNotCreateHomSpace : DimensionNinetyCreatesHomSpace → ⊥
dimensionDoesNotCreateHomSpace ()

cocycleTheoremDoesNotCreateActualLift :
  CocycleCancellationCreatesActualCocycleLift → ⊥
cocycleTheoremDoesNotCreateActualLift ()

noPermutationDoesNotCreateLinearIntertwiner :
  NoPermutationCreatesLinearIntertwiner → ⊥
noPermutationDoesNotCreateLinearIntertwiner ()

qidDoesNotCreateHomSpace : QidCreatesHomSpace → ⊥
qidDoesNotCreateHomSpace ()

deweyDoesNotCreateHomSpace : DeweyCreatesHomSpace → ⊥
deweyDoesNotCreateHomSpace ()

oeisDoesNotCreateHomSpace : OeisCreatesHomSpace → ⊥
oeisDoesNotCreateHomSpace ()

------------------------------------------------------------------------
-- 5. External coordinates remain navigation only.
------------------------------------------------------------------------

record HomSpaceExternalCoordinates : Set where
  constructor hom-space-external-coordinates
  field
    groupRepresentationQid : String
    representationCharacterQid : String
    groupRepresentationDewey : String
    finiteGroupDewey : String
    oeisCoordinate : String
    oeisHasHomSpaceAuthority : Bool
open HomSpaceExternalCoordinates public

canonicalHomSpaceExternalCoordinates : HomSpaceExternalCoordinates
canonicalHomSpaceExternalCoordinates = hom-space-external-coordinates
  "Q1055807"
  "Q600043"
  "512.22"
  "512.23"
  "not applicable: Hom-space/evaluation intertwiners are representation-theoretic objects, not integer-sequence evidence"
  false

------------------------------------------------------------------------
-- 6. Frontier.
------------------------------------------------------------------------

record LinearMultiplicityHomFrontier : Set where
  constructor linear-multiplicity-hom-frontier
  field
    canonicalHomSpaceRouteNamed : Bool
    finiteEvaluationDonorAvailable : Bool
    cocycleCancellationTheoremAvailable : Bool
    sourcePaidTwelvePlusSeventyEightCharacterAvailable : Bool
    pureFinNinetyPermutationRouteRefuted : Bool
    actualEquivariantHomCarrierConstructed : Bool
    actualLinearEvaluationInverseConstructed : Bool
    actualCocycleLiftInstantiated : Bool
    actualLinearMultiplicityRepresentationPaid : Bool
    nextResidual : String
open LinearMultiplicityHomFrontier public

currentLinearMultiplicityHomFrontier : LinearMultiplicityHomFrontier
currentLinearMultiplicityHomFrontier = linear-multiplicity-hom-frontier
  true true true true true
  false false false false
  "construct the actual representation-layer objects H_zeta and W_zeta as linear carriers and define S_zeta = Hom_E(H_zeta,W_zeta) on those same objects. Use ActualLinearWeightHomSpace and Frame.evaluate/Frame.recover for the full linear finite-copy map (not the historical Cartesian pair inverse), then instantiate the existing projective-cocycle cancellation owner with this exact S_zeta. The source-paid chi_12+chi_78 character and generic mathlib isotypic compiler apply only after that same-object linear weld. Do not reuse the finite X6 x Fin90 basis evaluation as the linear Hom evaluation."

characterFrontier : Character.PhaseCharacterWeldFrontier
characterFrontier = Character.currentPhaseCharacterWeldFrontier

wrongTypeFrontier : WrongType.MultiplicityWrongTypeFrontier
wrongTypeFrontier = WrongType.currentMultiplicityWrongTypeFrontier

noGoFrontier : NoGo.SuzukiNinetyPermutationNoGoFrontier
noGoFrontier = NoGo.currentSuzukiNinetyPermutationNoGoFrontier
