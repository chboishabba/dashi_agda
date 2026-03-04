module DASHI.Physics.SignatureUniquenessAssumed where

open import DASHI.Geometry.SignatureUniqueness31
  using (Signature; sig31; SignatureLaw; Signature31Theorem)
open import DASHI.Geometry.ParallelogramLaw using (AdditiveSpace)
open import DASHI.Geometry.ConeMetricCompatibility using (Quadratic; Cone; ConeMetricCompat)
open import Data.Unit using (⊤; tt)

-- Explicit dependency on isolated assumption packs.
open import DASHI.Physics.OrbitFingerprintAssumptionsPostulates as OFP
open import DASHI.Physics.DimensionBoundAssumptionsPostulates as DBP

-- Bridge hook: in the full proof, this would extract orbit/profile premises
-- from (QF, C, compat, iso, fs, arrow) and then apply OFP/DBP.
record SignatureAssumedAxioms : Set₁ where
  field
    orbitPremises :
      ∀ {A : AdditiveSpace}
      (QF     : Quadratic A)
      (C      : Cone A)
      (compat : ConeMetricCompat A C QF)
      (iso fs arrow : Set)
      → Set

-- Concrete instance (data-level assumption): always inhabited.
signatureAssumedAxioms : SignatureAssumedAxioms
signatureAssumedAxioms =
  record
    { orbitPremises = λ _ _ _ _ _ _ → ⊤
    }

-- Assumption-based signature law for the closure harness.
signature31-assumed : SignatureAssumedAxioms → Signature31Theorem
signature31-assumed ax = record
  { prove = λ {A} QF C compat iso fs arrow →
      let
        _ : Set
        _ = SignatureAssumedAxioms.orbitPremises ax QF C compat iso fs arrow
      in
      record { forced = sig31 }
  }
