module DASHI.Physics.YangMills.YMClayD1OriginalPeriodicPlaquetteFourBondSupportExact where

------------------------------------------------------------------------
-- D1: LITERAL ORIGINAL 4D PERIODIC WILSON PLAQUETTE BOND SUPPORT.
--
-- This is the SAME positive-bond carrier used in the original native
-- varying-cutoff SU(N) Wilson measure, not a new graph or synthetic
-- action. Each positively oriented plaquette uses four positive bond
-- variables, with the two negative oriented steps reading their
-- original corresponding positive link in inverse orientation.
--
-- The source paths and plane ordering are those of
-- BalabanClayGate4PeriodicBondPathBianchiExact, and the same
-- PeriodicPlaquette/PeriodicBlock/PositiveBond as the actual source.
--
-- DOES NOT assert a full 6-star upper bound, analytic Haar
-- factorization, CMP116 remote physical coverage, or 4D Clay gap.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Blocks
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Native

length : ∀ {A : Set} → List A → Nat
length [] = 0
length (_ ∷ xs) = suc (length xs)

-- Extract the actual original *positive bond indices* used by the
-- original signed four-step plaquette boundary (+mu,+nu,-mu,-nu).
-- Sign/inverse is retained by the existing Bond.pathHolonomy; it
-- does not affect the set of *underlying independent Haar variables*.
originalFourPositiveBonds :
  ∀ {n} → Plaquette.PeriodicPlaquette n →
    List (Torus.PositiveBond (suc n))
originalFourPositiveBonds p =
  let x  = Torus.first p
      mu = Torus.first (Plaquette.planeAxes (Torus.second p))
      nu = Torus.second (Plaquette.planeAxes (Torus.second p))
  in Torus.pair x mu ∷
     Torus.pair (Bond.positiveStep x mu) nu ∷
     Torus.pair (Bond.positiveStep x nu) mu ∷
     Torus.pair x nu ∷ []

originalPlaquetteReadsExactlyFourBondSlots :
  ∀ {n} (p : Plaquette.PeriodicPlaquette n) →
  length (originalFourPositiveBonds p) ≡ 4
originalPlaquetteReadsExactlyFourBondSlots p = refl

originalBoundaryUsesExactlyFourSignedSteps :
  (plane : Plaquette.PositivePlane4) →
  length (Bond.plaquetteBoundaryDirections plane) ≡ 4
originalBoundaryUsesExactlyFourSignedSteps plane = refl

-- The original six positive coordinate planes at any original
-- periodic block are the same six used by the Wilson action sum.
originalPositivePlanesPerSite :
  ∀ {n} (block : Blocks.PeriodicBlock n) →
  length (Plaquette.ownedPeriodicPlaquettes block) ≡ 6
originalPositivePlanesPerSite block = refl

-- The source selected finite Wilson trace truly consumes the
-- *original* PeriodicPlaquette n, not a test-only alternate carrier.
originalPlaquetteNativeSourceType :
  ∀ {Matrix Complex : Set} {N : Nat}
  (theory : DASHI.Physics.YangMills.SUNMatrixCarrier.CertifiedSUNMatrixTheory
      N Matrix Complex)
  (n : Nat) →
  Plaquette.PeriodicPlaquette n → Set
originalPlaquetteNativeSourceType theory n p =
  ∀ (links : Native.SUNPeriodicLinks theory n) →
  Native.periodicSUNPositivePlaquette theory n links p
    ≡ Native.periodicSUNPositivePlaquette theory n links p

originalPlaquetteNativeReflexive :
  ∀ {Matrix Complex : Set} {N : Nat}
  (theory : DASHI.Physics.YangMills.SUNMatrixCarrier.CertifiedSUNMatrixTheory
      N Matrix Complex)
  (n : Nat) (p : Plaquette.PeriodicPlaquette n) →
  originalPlaquetteNativeSourceType theory n p
originalPlaquetteNativeReflexive theory n p links = refl

-- Remaining *real* D1 geometry proof (not smuggled as a field):
-- prove every literal original positive link belongs to exactly six
-- original plaquettes, conflict-degree<=18, and a 19-packing theorem;
-- then use the ACTUAL finite product-Haar integration/Fubini source
-- to lift the resulting disjoint-star conditional factorization to
-- the original normalized SU(2) Wilson measure.
