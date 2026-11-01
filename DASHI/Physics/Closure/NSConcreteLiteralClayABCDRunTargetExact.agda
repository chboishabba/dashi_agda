module DASHI.Physics.Closure.NSConcreteLiteralClayABCDRunTargetExact where

------------------------------------------------------------------------
-- CONCRETE LITERAL NAVIER--STOKES A/B/C/D RUN TARGET
--
-- This is the terminal Agda surface after semantic hardening.  The caller no
-- longer chooses arbitrary meanings for Navier--Stokes predicates or any of
-- the four Clay carriers.  One FeffermanAnalyticKernel supplies only the
-- calculus/measure backend; NSConcreteFeffermanSemanticsExact fixes the PDE,
-- divergence, periodicity, decay, initial trace and bounded-energy predicates.
--
-- The four literal alternatives then live on the one fully canonical ABCD
-- instance.  Supplying any literal theorem gives the actual run target.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSClayLiteralABCDExact as Clay
import DASHI.Physics.Closure.NSConcreteFeffermanSemanticsExact as Concrete
import DASHI.Physics.Closure.NSCanonicalEuclideanPeriodicSemanticCarriersExact as Canonical
import DASHI.Physics.Closure.NSFullyCanonicalLiteralABCDInstanceExact as Fully

concreteSemantics :
  Concrete.FeffermanAnalyticKernel →
  Canonical.CanonicalNSSemantics
concreteSemantics = Concrete.concreteNSSemantics

concreteInstance :
  Concrete.FeffermanAnalyticKernel →
  Clay.LiteralClayABCDInstance
concreteInstance K =
  Fully.fullyCanonicalLiteralABCDInstance
    (concreteSemantics K)

LiteralA :
  Concrete.FeffermanAnalyticKernel → Set₁
LiteralA K =
  Clay.FeffermanEuclideanClayStatementA
    (Canonical.canonicalEuclideanA (concreteSemantics K))

LiteralB :
  Concrete.FeffermanAnalyticKernel → Set₁
LiteralB K =
  Clay.FeffermanPeriodicClayStatementB
    (Canonical.canonicalPeriodicB (concreteSemantics K))

LiteralC :
  Concrete.FeffermanAnalyticKernel → Set₁
LiteralC K =
  Clay.FeffermanEuclideanClayStatementC
    (Canonical.canonicalEuclideanC (concreteSemantics K))

LiteralD :
  Concrete.FeffermanAnalyticKernel → Set₁
LiteralD K =
  Clay.FeffermanPeriodicClayStatementD
    (Canonical.canonicalPeriodicD (concreteSemantics K))

record ConcreteLiteralNSRunTarget
    (K : Concrete.FeffermanAnalyticKernel) : Set₂ where
  field
    resolution :
      Clay.AnyOneClayResolution
        (concreteInstance K)

open ConcreteLiteralNSRunTarget public

runTargetFromA :
  ∀ {K} →
  LiteralA K →
  ConcreteLiteralNSRunTarget K
runTargetFromA proof =
  record
    { resolution =
        Fully.fullyCanonicalAResolution proof
    }

runTargetFromB :
  ∀ {K} →
  LiteralB K →
  ConcreteLiteralNSRunTarget K
runTargetFromB proof =
  record
    { resolution =
        Fully.fullyCanonicalBResolution proof
    }

runTargetFromC :
  ∀ {K} →
  LiteralC K →
  ConcreteLiteralNSRunTarget K
runTargetFromC proof =
  record
    { resolution =
        Fully.fullyCanonicalCResolution proof
    }

runTargetFromD :
  ∀ {K} →
  LiteralD K →
  ConcreteLiteralNSRunTarget K
runTargetFromD proof =
  record
    { resolution =
        Fully.fullyCanonicalDResolution proof
    }

record ConcreteLiteralABCDNativeProofs
    (K : Concrete.FeffermanAnalyticKernel) : Set₂ where
  field
    proofA : LiteralA K
    proofB : LiteralB K
    proofC : LiteralC K
    proofD : LiteralD K

open ConcreteLiteralABCDNativeProofs public

nativeAllFourToCompletion :
  ∀ {K} →
  ConcreteLiteralABCDNativeProofs K →
  Clay.LiteralFourAlternativeCompletion
    (concreteInstance K)
nativeAllFourToCompletion proofs = record
  { Clay.proofA = proofA proofs
  ; Clay.proofB = proofB proofs
  ; Clay.proofC = proofC proofs
  ; Clay.proofD = proofD proofs
  }

nativeAllFourToRunTarget :
  ∀ {K} →
  ConcreteLiteralABCDNativeProofs K →
  ConcreteLiteralNSRunTarget K
nativeAllFourToRunTarget proofs =
  record
    { resolution =
        Clay.literalAllFourImpliesAnyOne
          (nativeAllFourToCompletion proofs)
    }

------------------------------------------------------------------------
-- Foreign-kernel boundary remains proof-bearing.
------------------------------------------------------------------------

record ConcreteLiteralCDKernelBridge
    (K : Concrete.FeffermanAnalyticKernel) : Set₂ where
  field
    proofC : LiteralC K
    proofD : LiteralD K

open ConcreteLiteralCDKernelBridge public

runTargetFromCDKernelBridgeC :
  ∀ {K} →
  ConcreteLiteralCDKernelBridge K →
  ConcreteLiteralNSRunTarget K
runTargetFromCDKernelBridgeC bridge =
  runTargetFromC (ConcreteLiteralCDKernelBridge.proofC bridge)

runTargetFromCDKernelBridgeD :
  ∀ {K} →
  ConcreteLiteralCDKernelBridge K →
  ConcreteLiteralNSRunTarget K
runTargetFromCDKernelBridgeD bridge =
  runTargetFromD (ConcreteLiteralCDKernelBridge.proofD bridge)

arbitraryCanonicalSemanticsSelectableAtTerminalBoundary : Bool
arbitraryCanonicalSemanticsSelectableAtTerminalBoundary = false

arbitraryPeriodicBCarrierSelectableAtTerminalBoundary : Bool
arbitraryPeriodicBCarrierSelectableAtTerminalBoundary = false

literalABCDTheoremTypesMaterialized : Bool
literalABCDTheoremTypesMaterialized = true

foreignHashCountsAsProof : Bool
foreignHashCountsAsProof = false

clayPromotionWithoutProofTerm : Bool
clayPromotionWithoutProofTerm = false

arbitraryCanonicalSemanticsSelectableAtTerminalBoundaryIsFalse :
  arbitraryCanonicalSemanticsSelectableAtTerminalBoundary ≡ false
arbitraryCanonicalSemanticsSelectableAtTerminalBoundaryIsFalse = refl

arbitraryPeriodicBCarrierSelectableAtTerminalBoundaryIsFalse :
  arbitraryPeriodicBCarrierSelectableAtTerminalBoundary ≡ false
arbitraryPeriodicBCarrierSelectableAtTerminalBoundaryIsFalse = refl

literalABCDTheoremTypesMaterializedIsTrue :
  literalABCDTheoremTypesMaterialized ≡ true
literalABCDTheoremTypesMaterializedIsTrue = refl

foreignHashCountsAsProofIsFalse :
  foreignHashCountsAsProof ≡ false
foreignHashCountsAsProofIsFalse = refl
