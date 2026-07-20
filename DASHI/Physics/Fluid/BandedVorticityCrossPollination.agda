module DASHI.Physics.Fluid.BandedVorticityCrossPollination where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤)
open import Data.Vec using () renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)

open import DASHI.Foundations.SSPTritCarrier using
  (SSPTrit; sspNegOne; sspZero; sspPosOne)
open import DASHI.Geometry.SSP369Ultrametric using
  (Address; digit3; digit6; digit9; distance; distance-self-zero)
open import DASHI.Algebra.LieGaugeTheoryParity using
  (GaugeTheoryFeature; lieAlgebraFeature; representationFeature;
   connectionFeature; curvatureFeature; ObligationKind;
   equivarianceObligation; connectionNaturalityObligation;
   curvatureBianchiObligation)
open import DASHI.Physics.Fluid.BandedVorticitySpinTwist

------------------------------------------------------------------------
-- Cross-pollination surface for the banded vorticity carrier.
--
-- This module deliberately joins existing DASHI ideas without identifying
-- them.  In particular:
--
-- * support/sign factorisation is exact for the finite trit carrier;
-- * sign reversal is an involutive discrete symmetry;
-- * 3/6/9 addresses provide a finite hierarchical coordinate adapter;
-- * atom tracks provide the temporal/world-tube information absent from a
--   frame-local residual summary;
-- * MDL/action values select a representation but are not themselves fluid
--   energy or a Navier--Stokes Lyapunov theorem;
-- * Lie/gauge features are obligation sockets, not a claim that a trit is a
--   continuum Lie algebra element or that vorticity is Yang--Mills curvature.

------------------------------------------------------------------------
-- 1. Exact support/sign factorisation

data ActiveOrientation : Set where
  negativeOrientation : ActiveOrientation
  positiveOrientation : ActiveOrientation

data SupportSign : Set where
  unsupportedNeutral : SupportSign
  supported : ActiveOrientation → SupportSign

factorSpin : SSPTrit → SupportSign
factorSpin sspNegOne = supported negativeOrientation
factorSpin sspZero = unsupportedNeutral
factorSpin sspPosOne = supported positiveOrientation

assembleSpin : SupportSign → SSPTrit
assembleSpin unsupportedNeutral = sspZero
assembleSpin (supported negativeOrientation) = sspNegOne
assembleSpin (supported positiveOrientation) = sspPosOne

assemble-factor : ∀ t → assembleSpin (factorSpin t) ≡ t
assemble-factor sspNegOne = refl
assemble-factor sspZero = refl
assemble-factor sspPosOne = refl

factor-assemble : ∀ s → factorSpin (assembleSpin s) ≡ s
factor-assemble unsupportedNeutral = refl
factor-assemble (supported negativeOrientation) = refl
factor-assemble (supported positiveOrientation) = refl

------------------------------------------------------------------------
-- 2. Involution / mirror symmetry

mirrorOrientation : ActiveOrientation → ActiveOrientation
mirrorOrientation negativeOrientation = positiveOrientation
mirrorOrientation positiveOrientation = negativeOrientation

mirrorSupportSign : SupportSign → SupportSign
mirrorSupportSign unsupportedNeutral = unsupportedNeutral
mirrorSupportSign (supported o) = supported (mirrorOrientation o)

mirrorSpin : SSPTrit → SSPTrit
mirrorSpin t = assembleSpin (mirrorSupportSign (factorSpin t))

mirrorSpin-involutive : ∀ t → mirrorSpin (mirrorSpin t) ≡ t
mirrorSpin-involutive sspNegOne = refl
mirrorSpin-involutive sspZero = refl
mirrorSpin-involutive sspPosOne = refl

mirrorAtom : VortexAtom → VortexAtom
mirrorAtom a =
  vortexAtom
    (atomBand a)
    (atomSite a)
    (mirrorSpin (atomSpin a))
    (mirrorSupportProof (atomSpin a) (atomIsSupported a))
    (atomCoreScale a)
    (atomCirculationLevel a)
  where
    mirrorSupportProof :
      ∀ t → spinSupport t ≡ true → spinSupport (mirrorSpin t) ≡ true
    mirrorSupportProof sspNegOne p = refl
    mirrorSupportProof sspZero ()
    mirrorSupportProof sspPosOne p = refl

------------------------------------------------------------------------
-- 3. Hierarchical 3/6/9 address adapter
--
-- This is an explicit coordinate embedding only.  It does not assert that
-- low/mid/high physically equal the numerals 3/6/9.

BandAddress : Set
BandAddress = Address 1

bandAddress : ScaleBand → BandAddress
bandAddress lowBand = digit3 ∷ᵥ []ᵥ
bandAddress midBand = digit6 ∷ᵥ []ᵥ
bandAddress highBand = digit9 ∷ᵥ []ᵥ

bandAddressSelfDistanceZero :
  ∀ b → distance (bandAddress b) (bandAddress b) ≡ 0
bandAddressSelfDistanceZero b = distance-self-zero (bandAddress b)

record AddressedVortexAtom : Set where
  constructor addressedAtom
  field
    addressedVortex : VortexAtom
    hierarchicalBandAddress : BandAddress
    addressMatchesBand : hierarchicalBandAddress ≡ bandAddress (atomBand addressedVortex)
open AddressedVortexAtom public

addressVortex : VortexAtom → AddressedVortexAtom
addressVortex a = addressedAtom a (bandAddress (atomBand a)) refl

------------------------------------------------------------------------
-- 4. Temporal coherence / vortex world-tube

record TimedVortexAtom : Set where
  constructor timedAtom
  field
    atomTime : Nat
    atomIdentity : Nat
    timedVortex : VortexAtom
open TimedVortexAtom public

record VortexWorldTube : Set where
  constructor vortexWorldTube
  field
    tubeIdentity : Nat
    tubeSamples : List TimedVortexAtom
    tubeDescription : String
    tubeIdentityIsModelled : Bool
    tubeIdentityIsExactContinuumFact : Bool
open VortexWorldTube public

mkCandidateVortexWorldTube :
  Nat → List TimedVortexAtom → String → VortexWorldTube
mkCandidateVortexWorldTube identity samples description =
  vortexWorldTube identity samples description true false

------------------------------------------------------------------------
-- 5. MDL/action representation selection

record SolverSelectionReceipt : Set where
  constructor solverSelection
  field
    fastDescriptionLength : Nat
    faithfulDescriptionLength : Nat
    lostCoherencePenalty : Nat
    selectedSolverMode : SolverMode
    selectionObjectiveDescription : String
    objectiveExternallySupplied : Bool
open SolverSelectionReceipt public

-- The receipt records the decision inputs.  It does not conflate description
-- length with kinetic energy, enstrophy, entropy, or a monotone PDE action.
mkExternalSolverSelection :
  Nat → Nat → Nat → SolverMode → String → SolverSelectionReceipt
mkExternalSolverSelection fastLength faithfulLength penalty mode objective =
  solverSelection fastLength faithfulLength penalty mode objective true

------------------------------------------------------------------------
-- 6. Lie/gauge interface cross-reference

vorticityLieGaugeFeatureSockets : List GaugeTheoryFeature
vorticityLieGaugeFeatureSockets =
  lieAlgebraFeature
  ∷ representationFeature
  ∷ connectionFeature
  ∷ curvatureFeature
  ∷ []

vorticityLieGaugeOpenObligations : List ObligationKind
vorticityLieGaugeOpenObligations =
  equivarianceObligation
  ∷ connectionNaturalityObligation
  ∷ curvatureBianchiObligation
  ∷ []

------------------------------------------------------------------------
-- 7. Promotion boundary

data CrossPollinationClaim : Set where
  finiteSupportSignClaim : CrossPollinationClaim
  finiteMirrorSymmetryClaim : CrossPollinationClaim
  hierarchicalAddressClaim : CrossPollinationClaim
  candidateWorldTubeClaim : CrossPollinationClaim
  mdlSelectionReceiptClaim : CrossPollinationClaim
  continuumLieVorticityEquivalenceClaim : CrossPollinationClaim
  navierStokesClosureClaim : CrossPollinationClaim

ClaimAdmissible : CrossPollinationClaim → Set
ClaimAdmissible finiteSupportSignClaim = ⊤
ClaimAdmissible finiteMirrorSymmetryClaim = ⊤
ClaimAdmissible hierarchicalAddressClaim = ⊤
ClaimAdmissible candidateWorldTubeClaim = ⊤
ClaimAdmissible mdlSelectionReceiptClaim = ⊤
ClaimAdmissible continuumLieVorticityEquivalenceClaim = Never
ClaimAdmissible navierStokesClosureClaim = Never

continuumLieVorticityEquivalenceRejected :
  ClaimAdmissible continuumLieVorticityEquivalenceClaim → Never
continuumLieVorticityEquivalenceRejected impossible = impossible

navierStokesClosureRejected :
  ClaimAdmissible navierStokesClosureClaim → Never
navierStokesClosureRejected impossible = impossible

canonicalCrossPollinationNotes : List String
canonicalCrossPollinationNotes =
  "support/sign is an exact finite factorisation of the canonical SSP trit"
  ∷ "mirrorSpin is a checked involution"
  ∷ "3/6/9 is used as a hierarchical address adapter, not a physical identity"
  ∷ "vortex world-tubes retain temporal identity hypotheses across frames"
  ∷ "MDL/action selects representations without becoming fluid energy"
  ∷ "Lie/gauge structures are reusable obligation sockets"
  ∷ "continuum Lie-vorticity equivalence and Navier--Stokes closure remain rejected"
  ∷ []
