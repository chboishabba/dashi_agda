module DASHI.Arithmetic.CertifiedPrimePairModulusExact where

------------------------------------------------------------------------
-- ARBITRARY CERTIFIED PRIME MODULI / +2 RESIDUE SYMMETRY
--
-- Historical mathematics: Eratosthenes, Brun, the Chinese remainder
-- theorem, Hardy--Littlewood prime-pair local factors.
--
-- Reuses:
--   Data.Nat.Primality: proof-bearing prime? decider.
--   DASHI.Analysis.NatPrimeCountingInstance: original Nat prime owner.
--   DASHI.Arithmetic.FinitePrimeProductSieveExact: finite mixed-radix
--     coordinate codecs; those codecs are NOT arithmetic CRT on their own.
--   DASHI.Geometry.SSP369TreeAutomorphism:
--     existing SSP unit action preserves its prime identity.
--
-- A new certified prime axis can be appended at ANY Nat p provided
-- Prime p is supplied; no enumeration restricted to SSP15 is assumed.
-- Actual pair-survival is computed with modulus (suc c), not by
-- merely relabeling a fixed SSP prime.
--
-- These are finite local filters and period theorems. They neither
-- produce all primes from a fixed SSP action, nor establish twin-prime
-- infinitude, a Hardy--Littlewood estimate, or a general CRT isomorphism.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Fin.Base using (Fin)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using
  (_≢_; cong; trans; sym)
open import Data.Nat.Properties using (_≟_; +-assoc; +-comm)
open import Data.Nat.DivMod using (_%_; [m+n]%n≡m%n)
open import Data.Nat.Primality as NatPrime using (Prime; prime?)

import DASHI.Arithmetic.FinitePrimeProductSieveExact as Product
import DASHI.Arithmetic.PrimeModSixSieveExact as PrimeSix
import DASHI.Analysis.NatPrimeCountingInstance as NatCounter
import DASHI.Geometry.SSP369TreeAutomorphism as Tree
import DASHI.Foundations.SSPPrimeLane369Refinement as Ref
import DASHI.Foundations.SSPPrimeLaneUnitAction as SSPAction
import DASHI.TrackedPrimes as Tracked

two : Nat
two = suc (suc zero)

-- The factor c is p-1. Keeping the prime proof in the object avoids
-- treating arbitrary composite q as prime when extending the sieve.
record CertifiedPrimeAxis : Set where
  constructor certifiedPrimeAxis
  field
    nonzeroResidues : Nat
    primeWitness : Prime (suc nonzeroResidues)

open CertifiedPrimeAxis public

primeModulus : CertifiedPrimeAxis → Nat
primeModulus axis = suc (nonzeroResidues axis)

-- Reuse the same proof-bearing prime decider as NatPrimeCountingInstance.
-- Failure returns nothing rather than assigning prime status to a
-- candidate merely because its residue shape resembles an SSP lane.
certifyCandidate : (c : Nat) → Maybe CertifiedPrimeAxis
certifyCandidate c with NatPrime.prime? (suc c)
... | yes witness = just (certifiedPrimeAxis c witness)
... | no _ = nothing

-- The old counting layer is an independent full-Nat primality source.
-- It counts primes exactly; neither its index nor this classifier is
-- a fixed fifteen-lane SSP enumeration.
natPrimeCount : Nat → Nat
natPrimeCount = NatCounter.natPrimeCountLE

-- Finite prime lists feed the existing mixed-radix product codecs.
-- This equality is merely about the coordinate carrier cardinality,
-- NOT yet an arithmetic CRT theorem.
primeFactors : List CertifiedPrimeAxis → List Nat
primeFactors [] = []
primeFactors (axis ∷ rest) =
  nonzeroResidues axis ∷ primeFactors rest

ResidueProductCoordinates : List CertifiedPrimeAxis → Set
ResidueProductCoordinates axes =
  Product.ResidueCoordinates (primeFactors axes)

residueProductEncodeDecode :
  ∀ (axes : List CertifiedPrimeAxis)
    (code : Fin (Product.totalProduct (primeFactors axes))) →
  Product.encodeResidues
    (Product.decodeResidues code) ≡ code
residueProductEncodeDecode axes =
  Product.residueEncodeDecode

-- Local twin-offset filter at an arbitrary certified prime modulus.
-- The two coordinates are the actual n mod p and (n+2) mod p.
LocalPairSurvives : CertifiedPrimeAxis → Nat → Set
LocalPairSurvives axis n =
  (n % primeModulus axis ≢ zero)
  × ((n + two) % primeModulus axis ≢ zero)

-- This test is decidable for EVERY certified p, not just SSP15.
localPairSurvives? :
  (axis : CertifiedPrimeAxis) →
  (n : Nat) →
  Dec (LocalPairSurvives axis n)
localPairSurvives? axis n
  with (n % primeModulus axis) ≟ zero
     | ((n + two) % primeModulus axis) ≟ zero
... | yes zeroLeft | _ =
  no (λ pair → proj₁ pair zeroLeft)
... | no leftNonzero | yes zeroRight =
  no (λ pair → proj₂ pair zeroRight)
... | no leftNonzero | no rightNonzero =
  yes (leftNonzero , rightNonzero)

-- The inherited Nat modular arithmetic proves +p periodicity.
-- This is where arithmetic mod() symmetry enters. An orbit of
-- residue states stays over the SAME prime modulus p.
localModPeriod :
  (axis : CertifiedPrimeAxis) →
  (n : Nat) →
  (n + primeModulus axis) % primeModulus axis
    ≡ n % primeModulus axis
localModPeriod axis n =
  [m+n]%n≡m%n n (primeModulus axis)

addOffsetCommute :
  (n p : Nat) →
  (n + p) + two ≡ (n + two) + p
addOffsetCommute n p =
  trans (+-assoc n p two)
    (trans
      (cong (λ x → n + x) (+-comm p two))
      (sym (+-assoc n two p)))

localOffsetPeriod :
  (axis : CertifiedPrimeAxis) →
  (n : Nat) →
  ((n + primeModulus axis) + two) % primeModulus axis
    ≡ (n + two) % primeModulus axis
localOffsetPeriod axis n =
  trans
    (cong
      (λ x → x % primeModulus axis)
      (addOffsetCommute n (primeModulus axis)))
    ([m+n]%n≡m%n (n + two) (primeModulus axis))

localPairPeriodic :
  (axis : CertifiedPrimeAxis) →
  (n : Nat) →
  LocalPairSurvives axis n →
  LocalPairSurvives axis (n + primeModulus axis)
localPairPeriodic axis n (left , right) =
  (λ zeroAtShift →
    left (trans (sym (localModPeriod axis n)) zeroAtShift))
  ,
  (λ zeroAtShift →
    right (trans (sym (localOffsetPeriod axis n)) zeroAtShift))

localPairPeriodicBack :
  (axis : CertifiedPrimeAxis) →
  (n : Nat) →
  LocalPairSurvives axis (n + primeModulus axis) →
  LocalPairSurvives axis n
localPairPeriodicBack axis n (left , right) =
  (λ zeroAtBase →
    left (trans (localModPeriod axis n) zeroAtBase))
  ,
  (λ zeroAtBase →
    right (trans (localOffsetPeriod axis n) zeroAtBase))

-- Conjunction over an arbitrary finite list of *certified* prime axes.
-- A new prime refines the earlier test. It does not create new
-- false twin-prime evidence by undoing any old rejection.
AllPairSurvive : List CertifiedPrimeAxis → Nat → Set
AllPairSurvive [] n = ⊤
AllPairSurvive (axis ∷ rest) n =
  LocalPairSurvives axis n × AllPairSurvive rest n

extendPairSieve :
  (axis : CertifiedPrimeAxis) →
  (rest : List CertifiedPrimeAxis) →
  (n : Nat) →
  LocalPairSurvives axis n →
  AllPairSurvive rest n →
  AllPairSurvive (axis ∷ rest) n
extendPairSieve axis rest n current prior = current , prior

extendedSieveRetainsEarlier :
  (axis : CertifiedPrimeAxis) →
  (rest : List CertifiedPrimeAxis) →
  (n : Nat) →
  AllPairSurvive (axis ∷ rest) n →
  AllPairSurvive rest n
extendedSieveRetainsEarlier axis rest n = proj₂

extendedSieveValidatesNewPrime :
  (axis : CertifiedPrimeAxis) →
  (rest : List CertifiedPrimeAxis) →
  (n : Nat) →
  AllPairSurvive (axis ∷ rest) n →
  LocalPairSurvives axis n
extendedSieveValidatesNewPrime axis rest n = proj₁

-- Proof-bearing decision for an ARBITRARY finite sequence of
-- individually certified prime moduli. This consumes the local decider.
-- No fixed SSP15 lookup table is used.
allPairSurvive? :
  (axes : List CertifiedPrimeAxis) →
  (n : Nat) →
  Dec (AllPairSurvive axes n)
allPairSurvive? [] n = yes tt
allPairSurvive? (axis ∷ rest) n
  with localPairSurvives? axis n | allPairSurvive? rest n
... | yes localProof | yes remainingProof =
  yes (localProof , remainingProof)
... | no localFails | _ =
  no (λ complete → localFails (proj₁ complete))
... | yes localProof | no restFails =
  no (λ complete → restFails (proj₂ complete))

-- The new axis is a genuine prime because its witness is a
-- Data.Nat.Primality.Prime proof, not an SSP / C3 / 369 label.
axisReallyPrime :
  (axis : CertifiedPrimeAxis) →
  Prime (primeModulus axis)
axisReallyPrime axis = primeWitness axis

-- Reuse the canonical mod-six theorem: every prime >3 is in one of
-- two residue classes. The converse is intentionally NOT asserted.
sixWheelNecessaryForOtherPrimes :
  (n : Nat) →
  Prime (4 + n) →
  DASHI.Arithmetic.PrimeModSixSieveExact.PrimeModSixClass (4 + n)
sixWheelNecessaryForOtherPrimes =
  DASHI.Arithmetic.PrimeModSixSieveExact.primeAboveThreeModSix

-- The existing SSP symmetry acts on addresses and PRESERVES the
-- prime identity. This explicit reuse blocks a false inference that
-- rotating a fixed 15-prime address generates a new arithmetic prime.
sspAddressSymmetryPreservesPrime :
  ∀ {d : Nat} →
  (p : Tracked.SSP) →
  (step : SSPAction.UnitActionStep) →
  (r : Ref.SSPPrimeLane369Refinement d) →
  Ref.SSPPrimeLane369Refinement.primeLane
    (SSPAction.actOnRefinement p step r)
  ≡ Ref.SSPPrimeLane369Refinement.primeLane r
sspAddressSymmetryPreservesPrime = Tree.actionPreservesPrimeLane
