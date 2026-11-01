module DASHI.Core.CertifiedLatticeDescent where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Certified lattice descent.
--
-- This module formalises the DASHI analogue of constrained argmin.
-- It does not provide gradients, real-valued optimisation, convergence,
-- uniqueness, or empirical authority. A minimum is supplied together
-- with proofs that it is admissible and no more pressured than every
-- admissible competitor in the declared search fibre.

------------------------------------------------------------------------
-- A small proof-relevant order for finite structural pressure.

data _≤_ : Nat → Nat → Set where
  z≤n :
    {n : Nat} →
    zero ≤ n

  s≤s :
    {m n : Nat} →
    m ≤ n →
    suc m ≤ suc n

≤-refl :
  (n : Nat) →
  n ≤ n
≤-refl zero = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

------------------------------------------------------------------------
-- Pressure is split rather than collapsed so that descent cannot hide
-- which gate remains open.

record StructuralPressure : Set where
  constructor structuralPressure
  field
    receiptDeficit : Nat
    contradictionDeficit : Nat
    independenceDeficit : Nat
    temporalDeficit : Nat
    authorityDeficit : Nat
    promotionRisk : Nat

open StructuralPressure public

totalPressure :
  StructuralPressure →
  Nat
totalPressure p =
  receiptDeficit p
  + contradictionDeficit p
  + independenceDeficit p
  + temporalDeficit p
  + authorityDeficit p
  + promotionRisk p

------------------------------------------------------------------------
-- A state is a typed surface plus the observable pressure attached to it.
-- The carrier is abstract: this core can be instantiated by PNF receipts,
-- categorical projection surfaces, physics closures, or domain companions.

record DescentState (Carrier : Set) : Set where
  constructor descentState
  field
    carrier : Carrier
    pressure : StructuralPressure

open DescentState public

------------------------------------------------------------------------
-- Lawful refinements are positive witnesses. Each preservation statement
-- is carried as a Boolean together with a proof that it is true.

record AdmissibleRefinement
  {Carrier : Set}
  (from to : DescentState Carrier) : Set where
  constructor admissibleRefinement
  field
    receiptsPreserved : Bool
    receiptsPreservedIsTrue : receiptsPreserved ≡ true

    contradictionsPreserved : Bool
    contradictionsPreservedIsTrue : contradictionsPreserved ≡ true

    authorityBoundaryPreserved : Bool
    authorityBoundaryPreservedIsTrue :
      authorityBoundaryPreserved ≡ true

    promotionGatePreserved : Bool
    promotionGatePreservedIsTrue : promotionGatePreserved ≡ true

open AdmissibleRefinement public

record RefinementWitness
  {Carrier : Set}
  (from to : DescentState Carrier) : Set where
  constructor refinementWitness
  field
    admissible : AdmissibleRefinement from to
    nonIncreasingPressure :
      totalPressure (pressure to) ≤ totalPressure (pressure from)

open RefinementWitness public

------------------------------------------------------------------------
-- Projection is rejection-aware. An invalid proposal is not silently
-- repaired into a different claim; it remains explicitly rejected.

data ProjectionResult
  {Carrier : Set}
  (from proposal : DescentState Carrier) : Set where
  accepted :
    RefinementWitness from proposal →
    ProjectionResult from proposal

  rejected :
    String →
    ProjectionResult from proposal

projectAdmissible :
  {Carrier : Set} →
  {from proposal : DescentState Carrier} →
  RefinementWitness from proposal →
  ProjectionResult from proposal
projectAdmissible witness = accepted witness

rejectInadmissible :
  {Carrier : Set} →
  {from proposal : DescentState Carrier} →
  String →
  ProjectionResult from proposal
rejectInadmissible reason = rejected reason

------------------------------------------------------------------------
-- Proof-carrying constrained argmin.
--
-- SearchFibre describes exactly which candidate states are being compared.
-- The certificate proves:
--   * the chosen state belongs to the fibre,
--   * it is an admissible refinement of the source,
--   * every admissible competitor in that fibre has pressure at least as
--     large as the chosen state.
--
-- This is intentionally "a least admissible witness in a declared fibre",
-- not an unqualified global optimiser.

record CertifiedArgmin
  {Carrier : Set}
  (source : DescentState Carrier)
  (SearchFibre : DescentState Carrier → Set) : Set₁ where
  constructor certifiedArgmin
  field
    chosen : DescentState Carrier
    chosenInFibre : SearchFibre chosen
    chosenAdmissible : RefinementWitness source chosen
    leastAmongAdmissible :
      (competitor : DescentState Carrier) →
      SearchFibre competitor →
      RefinementWitness source competitor →
      totalPressure (pressure chosen)
      ≤
      totalPressure (pressure competitor)

open CertifiedArgmin public

argminState :
  {Carrier : Set} →
  {source : DescentState Carrier} →
  {SearchFibre : DescentState Carrier → Set} →
  CertifiedArgmin source SearchFibre →
  DescentState Carrier
argminState certificate = chosen certificate

------------------------------------------------------------------------
-- Descent receipt: keeps the mathematical result separate from promotion.

record CertifiedDescentReceipt
  {Carrier : Set}
  (source : DescentState Carrier)
  (SearchFibre : DescentState Carrier → Set) : Set₁ where
  constructor certifiedDescentReceipt
  field
    label : String
    argminCertificate : CertifiedArgmin source SearchFibre

    numericOptimizerImplemented : Bool
    numericOptimizerImplementedIsFalse :
      numericOptimizerImplemented ≡ false

    globalOptimalityClaimed : Bool
    globalOptimalityClaimedIsFalse :
      globalOptimalityClaimed ≡ false

    promotionAuthority : Bool
    promotionAuthorityIsFalse :
      promotionAuthority ≡ false

open CertifiedDescentReceipt public

mkNonPromotingDescentReceipt :
  {Carrier : Set} →
  {source : DescentState Carrier} →
  {SearchFibre : DescentState Carrier → Set} →
  String →
  CertifiedArgmin source SearchFibre →
  CertifiedDescentReceipt source SearchFibre
mkNonPromotingDescentReceipt label certificate =
  certifiedDescentReceipt
    label
    certificate
    false
    refl
    false
    refl
    false
    refl
