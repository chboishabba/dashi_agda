module DASHI.Topology.WormSoilPantsSheafBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.TemporalSheafProofObligations as Temporal

------------------------------------------------------------------------
-- Worm/soil replaces the misleading Euclidean Swiss-cheese picture.

data SupportRole : Set where
  wormPositive : SupportRole
  soilNegative : SupportRole

data CellStatus : Set where
  activeCell latentCell forbiddenCell unresolvedCell unobservedCell incompatibleCell collapsedCell : CellStatus

record ClopenCell : Set where
  constructor clopenCell
  field
    cellLabel : String
    depth : Nat
    supportRole : SupportRole
    status : CellStatus

open ClopenCell public

wormCell : ClopenCell
wormCell = clopenCell "realised trajectory packet" 2 wormPositive activeCell

soilCell : ClopenCell
soilCell = clopenCell "not-yet-traversed admissible medium" 2 soilNegative latentCell

record WormSoilPartition (Cell : Set) : Set₁ where
  field
    isWorm : Cell → Set
    isSoil : Cell → Set
    disjoint : ∀ cell → isWorm cell → isSoil cell → Set
    interpretation : String

------------------------------------------------------------------------
-- Pants are local tube branch/merge events, not a claim that a totally
-- disconnected p-adic fibre is itself a connected real surface.

data TubeEvent : Set where
  continueTube splitTube mergeTube reconnectTube dieBackTube : TubeEvent

record PantsJunction : Set where
  constructor pantsJunction
  field
    junctionLabel : String
    incomingTubes : Nat
    outgoingTubes : Nat
    event : TubeEvent
    phaseBoundaryRetained : Bool

canonicalSplitPants : PantsJunction
canonicalSplitPants = pantsJunction "one world-tube branches into two" 1 2 splitTube true

canonicalMergePants : PantsJunction
canonicalMergePants = pantsJunction "two local accounts merge into one compatible account" 2 1 mergeTube true

------------------------------------------------------------------------
-- Flexibility means an admissible deformation class exists while strand
-- identity and collision constraints remain explicit.

record BraidFlexibility : Set where
  constructor braidFlexibility
  field
    admissibleDeformationCount : Nat
    preservesStrandIdentity : Bool
    permitsRelativeReordering : Bool
    preventsIllegalCollision : Bool
    interpretation : String

open BraidFlexibility public

flexibleBraidProfile : BraidFlexibility
flexibleBraidProfile =
  braidFlexibility 9 true true true
    "sections may bend and exchange relative position through admitted chart changes while remaining distinguishable"

rigidDryBundleProfile : BraidFlexibility
rigidDryBundleProfile =
  braidFlexibility 1 true false true
    "parallel dry strands retain identity but do not yet carry enough deformation data to realise a braid"

data GluingOutcome : Set where
  gluesExactly needsFinerCover persistentObstruction : GluingOutcome

record NoodleGluingReceipt : Set where
  constructor noodleGluingReceipt
  field
    firstSection secondSection : String
    overlapDescription : String
    outcome : GluingOutcome
    flexibility : BraidFlexibility
    interpretation : String

refiningNoodleReceipt : NoodleGluingReceipt
refiningNoodleReceipt =
  noodleGluingReceipt
    "local section U"
    "local section V"
    "shared temporal-clopen packet"
    needsFinerCover
    flexibleBraidProfile
    "disagreement is preserved as a refinement request rather than forced into false global agreement"

------------------------------------------------------------------------
-- Explicit reuse of the existing fail-closed temporal and spacetime surfaces.

temporalSheafObligationSurface : Set₁
temporalSheafObligationSurface = Temporal.TemporalSheafObligation

spacetimeSheafObligationSurface : Set₁
spacetimeSheafObligationSurface = Temporal.SpacetimeSheafObligation

record WormSoilPantsBoundary : Set where
  constructor wormSoilPantsBoundary
  field
    wormIsPositiveSupport : Bool
    soilIsPotentialComplement : Bool
    negativeMeansForbiddenOnly : Bool
    negativeMeansForbiddenOnlyIsFalse : negativeMeansForbiddenOnly ≡ false
    pantsIsPadicFibreIdentity : Bool
    pantsIsPadicFibreIdentityIsFalse : pantsIsPadicFibreIdentity ≡ false
    drySpaghettiIsAlreadyASheaf : Bool
    drySpaghettiIsAlreadyASheafIsFalse : drySpaghettiIsAlreadyASheaf ≡ false
    fullBraidGroupActionPromoted : Bool
    fullBraidGroupActionPromotedIsFalse : fullBraidGroupActionPromoted ≡ false
    interpretation : String

canonicalWormSoilPantsBoundary : WormSoilPantsBoundary
canonicalWormSoilPantsBoundary =
  wormSoilPantsBoundary
    true
    true
    false refl
    false refl
    false refl
    false refl
    "worm tubes are realised positive support, soil is residual/latent medium, pants encode macroscopic branch geometry, and clopen p-adic data remains an internal fibre"
