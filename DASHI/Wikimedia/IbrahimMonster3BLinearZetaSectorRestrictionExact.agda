module DASHI.Wikimedia.IbrahimMonster3BLinearZetaSectorRestrictionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import DASHI.Moonshine.GradedRepresentation as GR

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Geometry.HilbertLorentzForcing as Linear
import DASHI.Moonshine.Monster3BCentralCharacterInertiaExact as Inertia
import DASHI.Moonshine.Base369Monster3BSingleActionProducerBidiExact as Single
import DASHI.Wikimedia.IbrahimMonster3BMultiplicityBasisLinearWrongTypeCorrectionExact as WrongType

------------------------------------------------------------------------
-- LINEAR RESTRICTION ON THE LITERAL MONSTER ZETA EIGENSECTOR
--
-- The existing single-action producer already makes the chosen zeta sector
-- literally equal to the dependent central eigenspace of one actual action.
-- What it does not carry is vector-space structure or linearity of the central
-- and normalizer maps.
--
-- This owner adds no second zeta carrier.  It states the exact same-object
-- restriction seam required before one may form the linear multiplicity Hom
-- space S_zeta = Hom_E(H_zeta,W_zeta):
--
--   * the ambient actual Monster state carrier is a linear carrier;
--   * central action, phase scaling and normalizer action are linear;
--   * the literal existing zeta eigenspace inherits a linear carrier;
--   * inertia restricts linearly to that same literal eigenspace.
--
-- Set-level phase resolution, character equality and dimension numerals do not
-- manufacture these witnesses.
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
  "primary representation-theoretic source for the central-character sectors and inertia-group character construction; not a machine-supplied linear carrier"
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
  "standard source calibration for invariant/eigenspace subrepresentations and linear group actions"
  Attribution.publicAttribution

barracloughWilsonAttribution = Snowball.canonicalSourceRoleSnowballReceipt barracloughWilson
serreAttribution = Snowball.canonicalSourceRoleSnowballReceipt serre

------------------------------------------------------------------------
-- Proof-bearing same-object seam.
------------------------------------------------------------------------

record LinearSingleActionProducer : Set₁ where
  field
    singleActionProducer : Single.ActualMonster3BSingleActionProducer

    ambientLinearCarrier : Linear.HilbertLift

    ambientCarrierIsActualState :
      Linear.Vector ambientLinearCarrier ≡ Single.State singleActionProducer

    -- Linearity proofs are deliberately explicit.  The generic set-level
    -- CentralNormalizerAction does not own them.
    centralActionIsLinear : Set
    normalizerActionIsLinear : Set
    phaseScalingIsLinear : Set

    -- This is the SAME literal eigenspace already chosen by the single-action
    -- producer, now equipped with inherited linear structure.
    zetaLinearCarrier : Linear.HilbertLift

    zetaCarrierIsLiteralEigenspace :
      Linear.Vector zetaLinearCarrier ≡ Single.literalZetaSector singleActionProducer

    inclusionIsLinear : Set
    inertiaRestrictionIsLinear : Set

open LinearSingleActionProducer public

------------------------------------------------------------------------
-- Full-vector successor.  The old SingleActionProducer requires a bijection
-- of the literal eigenspace with a finite basis.  That cannot be inhabited
-- by a nonzero K-vector space over Q(zeta).  Retain it for selected basis
-- recognition only, and put the original action and its linear laws first.
------------------------------------------------------------------------

record LiteralLinearNormalizerSource : Set₁ where
  field
    literalAmbient : Linear.HilbertLift
    literalNormalizer : Set
    literalGroup : GR.Group literalNormalizer
    literalNormalizerAction :
      Inertia.CentralNormalizerAction
        (Linear.Vector literalAmbient) literalNormalizer
    literalCentre : literalNormalizer
    centreIsSameAction : ∀ v →
      Inertia.centralAct (Inertia.phaseAction literalNormalizerAction) v
      ≡ Inertia.act literalNormalizerAction literalCentre v
    phaseScalar : Inertia.CentralPhase3 → Linear.Scalar literalAmbient
    phaseScaleIsScalar : ∀ p v →
      Inertia.phaseScale (Inertia.phaseAction literalNormalizerAction) p v
      ≡ Linear._·_ literalAmbient (phaseScalar p) v
    normalizerIdentity : ∀ v →
      Inertia.act literalNormalizerAction (GR.identity literalGroup) v ≡ v
    normalizerComposition : ∀ g h v →
      Inertia.act literalNormalizerAction (GR._∙_ literalGroup g h) v
      ≡ Inertia.act literalNormalizerAction g
          (Inertia.act literalNormalizerAction h v)
    normalizerZero : ∀ g →
      Inertia.act literalNormalizerAction g (Linear.zero literalAmbient)
      ≡ Linear.zero literalAmbient
    normalizerAdd : ∀ g u v →
      Inertia.act literalNormalizerAction g (Linear._+_ literalAmbient u v)
      ≡ Linear._+_ literalAmbient
          (Inertia.act literalNormalizerAction g u)
          (Inertia.act literalNormalizerAction g v)
    normalizerScale : ∀ g a v →
      Inertia.act literalNormalizerAction g (Linear._·_ literalAmbient a v)
      ≡ Linear._·_ literalAmbient a (Inertia.act literalNormalizerAction g v)

open LiteralLinearNormalizerSource public

-- All three restrictions may be taken on the SAME literal source.  No
-- Fin 90/729 basis recognition is required to define the full eigenspace.
record LiteralLinearPhaseRestriction
    (S : LiteralLinearNormalizerSource) (p : Inertia.CentralPhase3) : Set₁ where
  field
    phaseLinearCarrier : Linear.HilbertLift
    phaseVectorIsEigenspace :
      Linear.Vector phaseLinearCarrier ≡
      Inertia.CentralEigenspace
        (Inertia.phaseAction (literalNormalizerAction S)) p
    phaseScalarToAmbient :
      Linear.Scalar phaseLinearCarrier → Linear.Scalar (literalAmbient S)

  includePhase : Linear.Vector phaseLinearCarrier → Linear.Vector (literalAmbient S)
  includePhase v =
    Inertia.stateOf (subst (λ X → X) phaseVectorIsEigenspace v)

  restrictInertia : Inertia.CentralInertia (literalNormalizerAction S) →
    Linear.Vector phaseLinearCarrier → Linear.Vector phaseLinearCarrier
  restrictInertia g v =
    subst (λ X → X) (sym phaseVectorIsEigenspace)
      (Inertia.inertiaActsWithinPhase (literalNormalizerAction S) p g
        (subst (λ X → X) phaseVectorIsEigenspace v))

  field
    phaseIncludeZero :
      includePhase (Linear.zero phaseLinearCarrier) ≡ Linear.zero (literalAmbient S)
    phaseIncludeAdd : ∀ u v →
      includePhase (Linear._+_ phaseLinearCarrier u v)
      ≡ Linear._+_ (literalAmbient S) (includePhase u) (includePhase v)
    phaseIncludeScale : ∀ a v →
      includePhase (Linear._·_ phaseLinearCarrier a v)
      ≡ Linear._·_ (literalAmbient S) (phaseScalarToAmbient a) (includePhase v)
    phaseRestrictZero : ∀ g →
      restrictInertia g (Linear.zero phaseLinearCarrier) ≡ Linear.zero phaseLinearCarrier
    phaseRestrictAdd : ∀ g u v →
      restrictInertia g (Linear._+_ phaseLinearCarrier u v)
      ≡ Linear._+_ phaseLinearCarrier (restrictInertia g u) (restrictInertia g v)
    phaseRestrictScale : ∀ g a v →
      restrictInertia g (Linear._·_ phaseLinearCarrier a v)
      ≡ Linear._·_ phaseLinearCarrier a (restrictInertia g v)

open LiteralLinearPhaseRestriction public


------------------------------------------------------------------------
-- WrongType / non-promotion boundaries.
------------------------------------------------------------------------

data SetLevelPhaseResolutionCreatesLinearSector : Set where
data CharacterCreatesLinearSector : Set where
data DimensionCreatesLinearSector : Set where
data FiniteBasisCreatesActualLinearSector : Set where
data QidCreatesLinearRestriction : Set where
data DeweyCreatesLinearRestriction : Set where
data OeisCreatesLinearRestriction : Set where

setLevelPhaseResolutionDoesNotCreateLinearSector :
  SetLevelPhaseResolutionCreatesLinearSector → ⊥
setLevelPhaseResolutionDoesNotCreateLinearSector ()

characterDoesNotCreateLinearSector : CharacterCreatesLinearSector → ⊥
characterDoesNotCreateLinearSector ()

dimensionDoesNotCreateLinearSector : DimensionCreatesLinearSector → ⊥
dimensionDoesNotCreateLinearSector ()

finiteBasisDoesNotCreateActualLinearSector :
  FiniteBasisCreatesActualLinearSector → ⊥
finiteBasisDoesNotCreateActualLinearSector ()

qidDoesNotCreateLinearRestriction : QidCreatesLinearRestriction → ⊥
qidDoesNotCreateLinearRestriction ()

deweyDoesNotCreateLinearRestriction : DeweyCreatesLinearRestriction → ⊥
deweyDoesNotCreateLinearRestriction ()

oeisDoesNotCreateLinearRestriction : OeisCreatesLinearRestriction → ⊥
oeisDoesNotCreateLinearRestriction ()

------------------------------------------------------------------------
-- External classification coordinates remain navigation only.
------------------------------------------------------------------------

record LinearZetaExternalCoordinates : Set where
  constructor linear-zeta-external-coordinates
  field
    groupRepresentationQid : String
    representationCharacterQid : String
    groupRepresentationDewey : String
    finiteGroupDewey : String
    oeisCoordinate : String
    oeisHasLinearRestrictionAuthority : Bool
open LinearZetaExternalCoordinates public

canonicalLinearZetaExternalCoordinates : LinearZetaExternalCoordinates
canonicalLinearZetaExternalCoordinates = linear-zeta-external-coordinates
  "Q1055807"
  "Q600043"
  "512.22"
  "512.23"
  "not applicable: linear eigenspace restriction is representation structure, not integer-sequence evidence"
  false

------------------------------------------------------------------------
-- Frontier.
------------------------------------------------------------------------

record LinearZetaSectorFrontier : Set where
  constructor linear-zeta-sector-frontier
  field
    literalZetaEigenspaceAlreadyOwned : Bool
    separatePhaseSectorSearchNeeded : Bool
    ambientLinearMonsterCarrierPaid : Bool
    centralActionLinearityPaid : Bool
    normalizerActionLinearityPaid : Bool
    literalZetaLinearRestrictionPaid : Bool
    inertiaLinearRestrictionPaid : Bool
    actualLinearMultiplicityHomSpaceUnblocked : Bool
    nextResidual : String
open LinearZetaSectorFrontier public

currentLinearZetaSectorFrontier : LinearZetaSectorFrontier
currentLinearZetaSectorFrontier = linear-zeta-sector-frontier
  true false
  false false false false false false
  "attach the actual Monster weight-two/196883 representation's linear carrier to the SAME State used by ActualMonster3BSingleActionProducer and prove that the central phase map plus normalizer action evaluate as linear endomorphisms. Then the literal CentralEigenspace phaseZeta inherits the linear W_zeta carrier and the Hom-space construction S_zeta = Hom_E(H_zeta,W_zeta) becomes the next same-object compiler. Do not reconstruct a second sector from character or Fin90 basis data."

singleActionBoundary : Single.SingleActionProducerBoundary
singleActionBoundary = Single.canonicalSingleActionProducerBoundary

wrongTypeFrontier : WrongType.MultiplicityWrongTypeFrontier
wrongTypeFrontier = WrongType.currentMultiplicityWrongTypeFrontier
