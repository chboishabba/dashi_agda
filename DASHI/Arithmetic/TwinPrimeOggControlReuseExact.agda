module DASHI.Arithmetic.TwinPrimeOggControlReuseExact where

------------------------------------------------------------------------
-- Prior-art reuse for the user's SSP-generation hypothesis.
--
-- Existing authoritative owner:
-- DASHI.Moonshine.AllPrimeRepresentationFrickeClosureExact constructs
-- 20 prime-*control* rows below 72, including the 15 Ogg/SSP rows and
-- five non-Ogg control rows 37,43,53,61,67. These are not generated
-- by iterating the fixed-lane SSP369 automorphism.
--
-- New narrow integration: a control may supply an arithmetic sieve
-- axis only when a separate Data.Nat.Primality.Prime witness has
-- certified the same numeral. No Monster Fricke closure, representation
-- fingerprints, or character matching proves primality by itself.
--
-- Attribution: Ogg (1974-75), Duncan--Ono (2016); inherited DASHI
-- AllPrimeRepresentationFrickeClosureExact author/PR ownership.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)

import DASHI.Arithmetic.CertifiedPrimePairModulusExact as Certified
import DASHI.Moonshine.AllPrimeRepresentationFrickeClosureExact as AllPrime
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix

knownNonOggPrimeControls : List AllPrime.PrimeCandidateUnder72
knownNonOggPrimeControls =
  AllPrime.nonOggPrimeCandidatesUnder72

knownNonOggControlCount :
  Matrix.listCount knownNonOggPrimeControls ≡ 5
knownNonOggControlCount =
  AllPrime.nonOggPrimeCandidateCountIsFive

knownAllPrimeControlCount :
  Matrix.listCount AllPrime.allPrimeCandidatesUnder72 ≡ 20
knownAllPrimeControlCount =
  AllPrime.allPrimeCandidateCountIsTwenty

record ControlToCertifiedPrime : Set where
  constructor controlToCertifiedPrime
  field
    existingControl : AllPrime.PrimeCandidateUnder72
    certifiedAxis : Certified.CertifiedPrimeAxis
    sameArithmeticValue :
      AllPrime.primeCandidateLevel existingControl
      ≡ Certified.primeModulus certifiedAxis

open ControlToCertifiedPrime public

-- Exact value projection from a witnessed correspondence. This is
-- genuinely derived; it does NOT fabricate a Prime proof from the
-- representation/Fricke-control label.
controlAndCertifiedPrimeAgree :
  (bridge : ControlToCertifiedPrime) →
  AllPrime.primeCandidateLevel (existingControl bridge)
    ≡ Certified.primeModulus (certifiedAxis bridge)
controlAndCertifiedPrimeAgree = sameArithmeticValue
