module DASHI.Algebra.CliffordSpinLift where

open import Agda.Primitive using (Level; Setω; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

open import DASHI.Foundations.CausalOrderLorentzClosure

------------------------------------------------------------------------
-- Clifford / Pin / Spin closure generated from quadratic geometry.
--
-- The direction of explanation is intentionally explicit:
--
--   contractive multiscale closure
--     -> orthogonal decomposition
--     -> quadratic form
--     -> Clifford universal property
--     -> Pin/Spin units
--     -> Spin(p,q) -> SO(p,q) double cover.
--
-- Support projection is not presented as the origin of Spin.  It is only a
-- quotient/readout after the quadratic and Clifford structures are supplied.

record QuadraticSpace {ℓ : Level} : Set (lsuc ℓ) where
  field
    Scalar :
      Set ℓ

    Vector :
      Set ℓ

    zero :
      Vector

    add :
      Vector → Vector → Vector

    scale :
      Scalar → Vector → Vector

    Q :
      Vector → Scalar

    polar :
      Vector → Vector → Scalar

    nondegenerate :
      Bool

    signature :
      LorentzSignature31

open QuadraticSpace public

record AssociativeUnitalAlgebra {ℓ : Level} : Set (lsuc ℓ) where
  field
    Carrier :
      Set ℓ

    Scalar :
      Set ℓ

    zero :
      Carrier

    one :
      Carrier

    add :
      Carrier → Carrier → Carrier

    mul :
      Carrier → Carrier → Carrier

    scalar :
      Scalar → Carrier

    associative :
      Bool

    leftUnit :
      Bool

    rightUnit :
      Bool

open AssociativeUnitalAlgebra public

record CliffordAlgebra {ℓ : Level} (V : QuadraticSpace {ℓ}) :
  Set (lsuc ℓ) where
  open QuadraticSpace V
  field
    algebra :
      AssociativeUnitalAlgebra {ℓ}

    injectVector :
      Vector → AssociativeUnitalAlgebra.Carrier algebra

    cliffordRelation :
      Vector → Bool

    polarizedCliffordRelation :
      Vector → Vector → Bool

    universalTarget :
      AssociativeUnitalAlgebra {ℓ} → Set ℓ

    universalFactor :
      (A : AssociativeUnitalAlgebra {ℓ}) → universalTarget A → Set ℓ

    universalFactorExists :
      (A : AssociativeUnitalAlgebra {ℓ}) → universalTarget A → Bool

    universalFactorUnique :
      (A : AssociativeUnitalAlgebra {ℓ}) → universalTarget A → Bool

    explicitBasisAvailable :
      Bool

open CliffordAlgebra public

record PinSpinUnits {ℓ : Level}
  (V : QuadraticSpace {ℓ})
  (Cl : CliffordAlgebra V) : Set (lsuc ℓ) where
  field
    UnitVector :
      Set ℓ

    Pin :
      Set ℓ

    Spin :
      Set ℓ

    EvenClifford :
      Set ℓ

    pinGeneratedByUnitVectors :
      Bool

    spinGeneratedByEvenProducts :
      Bool

    spinContainedInEvenClifford :
      Bool

    inverseClosed :
      Bool

open PinSpinUnits public

record OrthogonalDoubleCover {ℓ : Level}
  (V : QuadraticSpace {ℓ})
  (Cl : CliffordAlgebra V)
  (U : PinSpinUnits V Cl) : Set (lsuc ℓ) where
  open QuadraticSpace V
  open PinSpinUnits U
  field
    SO :
      Set ℓ

    rho :
      Spin → SO

    rhoHomomorphism :
      Bool

    rhoSurjective :
      Bool

    kernelElementPositive :
      Spin

    kernelElementNegative :
      Spin

    kernelExactlyPlusMinusOne :
      Bool

    rhoTwoToOne :
      Bool

    twistedAdjointPreservesQ :
      Bool

open OrthogonalDoubleCover public

record Spin3SU2Representation {ℓ : Level} : Set (lsuc ℓ) where
  field
    Complex :
      Set ℓ

    Qubit :
      Set ℓ

    Qutrit :
      Set ℓ

    SU2 :
      Set ℓ

    Spin3 :
      Set ℓ

    spin3ToSU2 :
      Spin3 → SU2

    su2ToSpin3 :
      SU2 → Spin3

    spin3SU2InverseLaws :
      Bool

    qubitInsideQutrit :
      Qubit → Qutrit

    su2ActsOnQubit :
      SU2 → Qubit → Qubit

    optionalSpinOneActionOnQutrit :
      SU2 → Qutrit → Qutrit

    qubitActionUnitary :
      Bool

    qutritActionUnitary :
      Bool

open Spin3SU2Representation public

record CliffordSpinClosure : Setω where
  field
    level :
      Level

    quadraticSpace :
      QuadraticSpace {level}

    cliffordAlgebra :
      CliffordAlgebra quadraticSpace

    pinSpinUnits :
      PinSpinUnits quadraticSpace cliffordAlgebra

    orthogonalDoubleCover :
      OrthogonalDoubleCover quadraticSpace cliffordAlgebra pinSpinUnits

    spin3SU2Representation :
      Spin3SU2Representation {level}

    quadraticGeometryForcesCliffordCompletion :
      Bool

    involutionParitySelectsEvenPhysicalLift :
      Bool

    spinIsUniversalSymmetryLiftNotProjectionArtifact :
      Bool

    allCliffordSpinTheoremsDischarged :
      Bool

open CliffordSpinClosure public

record CliffordSpinReceipt : Set where
  field
    universalPropertyExplicit : Bool
    basisRelationsExplicit : Bool
    pinUnitsExplicit : Bool
    spinEvenSubalgebraExplicit : Bool
    rhoHomomorphismExplicit : Bool
    rhoSurjectivityExplicit : Bool
    rhoKernelExplicit : Bool
    spin3SU2ActionExplicit : Bool

canonicalCliffordSpinReceipt : CliffordSpinReceipt
canonicalCliffordSpinReceipt =
  record
    { universalPropertyExplicit = true
    ; basisRelationsExplicit = true
    ; pinUnitsExplicit = true
    ; spinEvenSubalgebraExplicit = true
    ; rhoHomomorphismExplicit = true
    ; rhoSurjectivityExplicit = true
    ; rhoKernelExplicit = true
    ; spin3SU2ActionExplicit = true
    }

cliffordSpinBoundaryText : String
cliffordSpinBoundaryText =
  "Spin is obtained from the universal Clifford completion of an already established quadratic geometry.  Support/sign projection may expose the quotient but is not the derivation of the Spin double cover."
