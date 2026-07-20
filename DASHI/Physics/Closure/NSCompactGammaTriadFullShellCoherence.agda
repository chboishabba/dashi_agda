module DASHI.Physics.Closure.NSCompactGammaTriadFullShellCoherence where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Primitive using (Level; _⊔_; lsuc)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPairIncidenceKernel as PairKernel
import DASHI.Physics.Closure.NSCompactGammaOffPacketTriadMajorization as Major
import DASHI.Physics.Closure.NSCompactGammaDifferentiatedTriadInstantiation as Triads
import DASHI.Physics.Closure.NSCompactGammaFullShellSchur as FullShell

------------------------------------------------------------------------
-- Coherence between the exact differentiated atom list and the exact pair fold
-- used by the full-shell Schur kernel.
------------------------------------------------------------------------

record TriadFullShellCoherence
    {p m v i : Level}
    {Pair : Set p}
    {Mode : Set m}
    {Vector : Set v}
    (A : AbsorptionArithmetic)
    (M : Major.FiniteMajorantArithmetic A)
    (triadsAt :
      Nat → Nat →
      Triads.DifferentiatedTriadAtomFamily Pair Mode Vector A M)
    (shell :
      FullShell.FullShellFourierFamily
        {i = i} Pair Mode (Scalar A)) :
    Set (lsuc (p ⊔ m ⊔ v ⊔ i)) where
  field
    pairListsMatch :
      ∀ K N →
      Triads.pairAtoms (triadsAt K N) ≡
      PairKernel.pairs (FullShell.pairDataAt shell K N)

    atomIncidence :
      ∀ K N pair →
      FullShell.OccursPair shell
        (PairKernel.pairs (FullShell.pairDataAt shell K N)) pair →
      FullShell.Incidence shell K N pair
        (Triads.targetMode (triadsAt K N) pair)
        (Triads.leftMode (triadsAt K N) pair)

    signedResponseMatchesFullShell :
      ∀ K N pair →
      Triads.signedTriadMagnitude (triadsAt K N) pair ≡
      FullShell.localFourierResponse shell K N pair

    localMajorantMatchesFullShell :
      ∀ K N pair →
      Triads.triadMajorant (triadsAt K N) pair ≡
      FullShell.localFourierMajorant shell K N pair

    nearResponseMatchesShellResponse :
      ∀ K N →
      Triads.concreteNearResponse (triadsAt K N) ≡
      Major.sumScalars A
        (DASHI.Analysis.FiniteWeightedKernelSums.map
          (FullShell.localFourierResponse shell K N)
          (PairKernel.pairs (FullShell.pairDataAt shell K N)))

    majorantActionMatchesShellFold :
      ∀ K N →
      Triads.majorantActionOutput (triadsAt K N) ≡
      Major.sumScalars A
        (DASHI.Analysis.FiniteWeightedKernelSums.map
          (FullShell.localFourierMajorant shell K N)
          (PairKernel.pairs (FullShell.pairDataAt shell K N)))

open TriadFullShellCoherence public

coherentLocalMajorization :
  ∀ {p m v i}
    {Pair : Set p}
    {Mode : Set m}
    {Vector : Set v}
    {A : AbsorptionArithmetic}
    {M : Major.FiniteMajorantArithmetic A}
    {triadsAt :
      Nat → Nat →
      Triads.DifferentiatedTriadAtomFamily Pair Mode Vector A M}
    {shell :
      FullShell.FullShellFourierFamily
        {i = i} Pair Mode (Scalar A)} →
  TriadFullShellCoherence A M triadsAt shell →
  ∀ K N pair →
  _≤_ A
    (Triads.signedTriadMagnitude (triadsAt K N) pair)
    (Triads.triadMajorant (triadsAt K N) pair)
coherentLocalMajorization C K N pair =
  Triads.localTriadMajorizationFromAnalyticLeaf _ pair
