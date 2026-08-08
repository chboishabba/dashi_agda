module DASHI.Physics.YangMills.BalabanP33CovariantD4TransportCocycleBoundaryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- John H. Conway and Derek A. Smith,
-- "On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry",
-- A K Peters, 2003.
-- DOI: 10.1201/9781439864180.
--
-- DASHI CONTRIBUTION
--
-- Keep the strict geometric D4 slot action separate from transport of actual
-- background-dependent link jets.  The latter may compose only up to an
-- explicit gauge/basepoint correction
--
--   T_g^A T_h^A = Gamma_A(g,h) T_(gh)^A.
--
-- Orbit reduction is therefore unavailable until the correction is proved
-- trivial or the estimate is proved invariant under it.  A strict action is
-- recovered as a theorem from a pointwise trivial-cocycle certificate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanWilsonD4SubsetCharacterExact as D4

record PointwiseEqual {X : Set} (left right : X → X) : Set where
  field
    at : ∀ value → left value ≡ right value

open PointwiseEqual public

record GeometricD4Action (X : Set) : Set₁ where
  field
    act : D4.SlotPermutation4 → X → X
    identityExact : ∀ value →
      act D4.identityPermutation4 value ≡ value
    compositionExact : ∀ left right value →
      act (D4.composePermutation4 left right) value
      ≡ act left (act right value)

open GeometricD4Action public

record CovariantD4Transport (Jet GaugeCorrection : Set) : Set₁ where
  field
    transport : D4.SlotPermutation4 → Jet → Jet
    correctionAction : GaugeCorrection → Jet → Jet
    correction :
      D4.SlotPermutation4 → D4.SlotPermutation4 → GaugeCorrection

    identityTransport : ∀ jet →
      transport D4.identityPermutation4 jet ≡ jet

    twistedComposition : ∀ left right jet →
      transport left (transport right jet)
      ≡ correctionAction (correction left right)
          (transport (D4.composePermutation4 left right) jet)

open CovariantD4Transport public

record TrivialTransportCocycle
    {Jet GaugeCorrection : Set}
    (data : CovariantD4Transport Jet GaugeCorrection) : Set₁ where
  field
    correctionActsTrivially : ∀ left right jet →
      correctionAction data (correction data left right)
        (transport data (D4.composePermutation4 left right) jet)
      ≡ transport data (D4.composePermutation4 left right) jet

open TrivialTransportCocycle public

strictCompositionFromTrivialCocycle :
  ∀ {Jet GaugeCorrection}
    {data : CovariantD4Transport Jet GaugeCorrection} →
  TrivialTransportCocycle data →
  ∀ left right jet →
  transport data left (transport data right jet)
  ≡ transport data (D4.composePermutation4 left right) jet
strictCompositionFromTrivialCocycle trivial left right jet =
  trans
    (twistedComposition data left right jet)
    (correctionActsTrivially trivial left right jet)

record CorrectionInvariantQuantity
    {Jet GaugeCorrection Value : Set}
    (data : CovariantD4Transport Jet GaugeCorrection)
    (quantity : Jet → Value) : Set₁ where
  field
    correctionInvariant : ∀ correctionValue jet →
      quantity (correctionAction data correctionValue jet)
      ≡ quantity jet

open CorrectionInvariantQuantity public

quantityTransportCompositionExact :
  ∀ {Jet GaugeCorrection Value}
    {data : CovariantD4Transport Jet GaugeCorrection}
    {quantity : Jet → Value} →
  CorrectionInvariantQuantity data quantity →
  ∀ left right jet →
  quantity (transport data left (transport data right jet))
  ≡ quantity
      (transport data (D4.composePermutation4 left right) jet)
quantityTransportCompositionExact invariant left right jet =
  trans
    (congQuantity
      (twistedComposition data left right jet))
    (correctionInvariant invariant
      (correction data left right)
      (transport data (D4.composePermutation4 left right) jet))
  where
  congQuantity : ∀ {x y} → x ≡ y → quantity x ≡ quantity y
  congQuantity refl = refl

data D4ActionKind : Set where
  geometricSlotPermutation covariantBackgroundTransport : D4ActionKind

geometricIsNotCovariant :
  geometricSlotPermutation ≡ covariantBackgroundTransport → ⊥
geometricIsNotCovariant ()

geometricD4ActionLevel : ProofLevel
geometricD4ActionLevel = machineChecked

covariantD4TwistedActionLevel : ProofLevel
covariantD4TwistedActionLevel = machineChecked

strictD4RecoveryRequiresTrivialCocycleLevel : ProofLevel
strictD4RecoveryRequiresTrivialCocycleLevel = machineChecked
