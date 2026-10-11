module DASHI.Analysis.CollatzSyracuseUniformWordDescentCertificateValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_)
import Data.Nat.Properties as NatP

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.Analysis.CollatzSyracuseEarlyCylinderEliminationExact as Early
import DASHI.Analysis.CollatzSyracuseUniformWordDescentCertificateExact as Cert

word1100 : Binary.BinaryWord 4
word1100 =
  Binary.bit1 (Binary.bit1 (Binary.bit0 (Binary.bit0 Binary.end)))

word11010 : Binary.BinaryWord 5
word11010 =
  Binary.bit1
    (Binary.bit1
      (Binary.bit0
        (Binary.bit1 (Binary.bit0 Binary.end))))

word11100 : Binary.BinaryWord 5
word11100 =
  Binary.bit1
    (Binary.bit1
      (Binary.bit1
        (Binary.bit0 (Binary.bit0 Binary.end))))

certificate1100 : Cert.UniformWordDescentCertificate word1100
certificate1100 = record
  { Cert.gap = 7
  ; Cert.minimumStart = 1
  ; Cert.denominatorSplit = refl
  ; Cert.correctionBelowGapAtMinimum = NatP.m≤m+n 6 1
  }

certificate11010 : Cert.UniformWordDescentCertificate word11010
certificate11010 = record
  { Cert.gap = 5
  ; Cert.minimumStart = 5
  ; Cert.denominatorSplit = refl
  ; Cert.correctionBelowGapAtMinimum = NatP.m≤m+n 24 1
  }

certificate11100 : Cert.UniformWordDescentCertificate word11100
certificate11100 = record
  { Cert.gap = 5
  ; Cert.minimumStart = 4
  ; Cert.denominatorSplit = refl
  ; Cert.correctionBelowGapAtMinimum = NatP.≤-refl
  }

genericPays1100 :
  (x : Syracuse.PositiveNat) →
  1 ≤ Syracuse.toNat x →
  Itinerary.parity x ≡ true →
  Itinerary.parity (Early.step1 x) ≡ true →
  Itinerary.parity (Early.step2 x) ≡ false →
  Itinerary.parity (Early.step3 x) ≡ false →
  Syracuse.toNat (Syracuse.syracuseIterate 4 x) < Syracuse.toNat x
genericPays1100 x lower p0 p1 p2 p3 =
  Cert.uniformWordCertificateImpliesDescent
    word1100 certificate1100 x lower
    (Early.word1100 x p0 p1 p2 p3)

genericPays11010 :
  (x : Syracuse.PositiveNat) →
  5 ≤ Syracuse.toNat x →
  Itinerary.parity x ≡ true →
  Itinerary.parity (Early.step1 x) ≡ true →
  Itinerary.parity (Early.step2 x) ≡ false →
  Itinerary.parity (Early.step3 x) ≡ true →
  Itinerary.parity (Early.step4 x) ≡ false →
  Syracuse.toNat (Syracuse.syracuseIterate 5 x) < Syracuse.toNat x
genericPays11010 x lower p0 p1 p2 p3 p4 =
  Cert.uniformWordCertificateImpliesDescent
    word11010 certificate11010 x lower
    (Early.word11010 x p0 p1 p2 p3 p4)

genericPays11100 :
  (x : Syracuse.PositiveNat) →
  4 ≤ Syracuse.toNat x →
  Itinerary.parity x ≡ true →
  Itinerary.parity (Early.step1 x) ≡ true →
  Itinerary.parity (Early.step2 x) ≡ true →
  Itinerary.parity (Early.step3 x) ≡ false →
  Itinerary.parity (Early.step4 x) ≡ false →
  Syracuse.toNat (Syracuse.syracuseIterate 5 x) < Syracuse.toNat x
genericPays11100 x lower p0 p1 p2 p3 p4 =
  Cert.uniformWordCertificateImpliesDescent
    word11100 certificate11100 x lower
    (Early.word11100 x p0 p1 p2 p3 p4)

genericCertificateCompilerPaid :
  Cert.UniformWordDescentCertificateBoundary.uniformThresholdCompilerPaid
    Cert.canonicalUniformWordDescentCertificateBoundary
  ≡ 1
genericCertificateCompilerPaid = refl
