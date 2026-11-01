module DASHI.Physics.YangMills.BalabanClayT5StagedDiagonalTailExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- Roman Kotecký and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions",
-- Communications in Mathematical Physics 31 (1973), 83--112.
-- DOI: 10.1007/BF01645738.
--
-- DASHI CONTRIBUTION
--
-- The previous thermodynamic producer kept a diagonal finite-volume/cutoff
-- tail as an independent physical input.  This module derives that diagonal
-- Cauchy tail from the two tails that actually arise in the RG construction:
--
--   finite volume at cutoff k  -> thermodynamic measure at cutoff k,
--   thermodynamic cutoff k     -> continuum measure.
--
-- If
--
--   d(F_k,T_k) <= v_k,
--   d(T_k,C)   <= c_k,
--
-- then
--
--   d(F_k,C) <= v_k + c_k
--
-- and, for two cutoffs l,r,
--
--   d(F_l,F_r)
--     <= (v_l+c_l) + (v_r+c_r)
--     <= 2 (v_min+c_min).
--
-- Thus the diagonal convergence witness is constructed from staged tails;
-- it is not a third independent analytic hypothesis.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as Thermo

record StagedDiagonalTailData
    (Scalar : Set)
    (Converges : (Nat → Scalar) → Scalar → Set)
    (finiteDiagonal thermodynamic : Nat → Scalar)
    (continuum : Scalar) : Set₁ where
  field
    Distance : Scalar → Scalar → Scalar
    zero : Scalar
    add : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left leftUpper right rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (add left right) (add leftUpper rightUpper)

    distanceTriangle : ∀ left middle right →
      LessEqual (Distance left right)
        (add (Distance left middle) (Distance middle right))
    distanceSymmetric : ∀ left right →
      LessEqual (Distance left right) (Distance right left)

    volumeTail cutoffTail : Nat → Scalar
    finiteToThermodynamic : ∀ cutoff →
      LessEqual
        (Distance (finiteDiagonal cutoff) (thermodynamic cutoff))
        (volumeTail cutoff)
    thermodynamicToContinuum : ∀ cutoff →
      LessEqual
        (Distance (thermodynamic cutoff) continuum)
        (cutoffTail cutoff)

    earlier : Nat → Nat → Nat
    combinedTailAntitoneLeft : ∀ left right →
      LessEqual
        (add (volumeTail left) (cutoffTail left))
        (add
          (volumeTail (earlier left right))
          (cutoffTail (earlier left right)))
    combinedTailAntitoneRight : ∀ left right →
      LessEqual
        (add (volumeTail right) (cutoffTail right))
        (add
          (volumeTail (earlier left right))
          (cutoffTail (earlier left right)))

    doubledCombinedTailVanishes : Set
    cauchyCompletionFromTail :
      (∀ left right →
        LessEqual
          (Distance (finiteDiagonal left) (finiteDiagonal right))
          (add
            (add
              (volumeTail (earlier left right))
              (cutoffTail (earlier left right)))
            (add
              (volumeTail (earlier left right))
              (cutoffTail (earlier left right))))) →
      doubledCombinedTailVanishes →
      Converges finiteDiagonal continuum

open StagedDiagonalTailData public

combinedTail :
  ∀ {Scalar Converges finiteDiagonal thermodynamic continuum} →
  StagedDiagonalTailData
    Scalar Converges finiteDiagonal thermodynamic continuum →
  Nat → Scalar
combinedTail dataSet cutoff =
  add dataSet (volumeTail dataSet cutoff) (cutoffTail dataSet cutoff)

doubledCombinedTail :
  ∀ {Scalar Converges finiteDiagonal thermodynamic continuum} →
  StagedDiagonalTailData
    Scalar Converges finiteDiagonal thermodynamic continuum →
  Nat → Scalar
doubledCombinedTail dataSet cutoff =
  add dataSet (combinedTail dataSet cutoff) (combinedTail dataSet cutoff)

finiteDiagonalToContinuum :
  ∀ {Scalar Converges finiteDiagonal thermodynamic continuum}
    (dataSet : StagedDiagonalTailData
      Scalar Converges finiteDiagonal thermodynamic continuum)
    cutoff →
  LessEqual dataSet
    (Distance dataSet (finiteDiagonal cutoff) continuum)
    (combinedTail dataSet cutoff)
finiteDiagonalToContinuum dataSet cutoff =
  transitive dataSet
    (distanceTriangle dataSet
      (finiteDiagonal cutoff) (thermodynamic cutoff) continuum)
    (addMonotone dataSet
      (finiteToThermodynamic dataSet cutoff)
      (thermodynamicToContinuum dataSet cutoff))

continuumToFiniteDiagonal :
  ∀ {Scalar Converges finiteDiagonal thermodynamic continuum}
    (dataSet : StagedDiagonalTailData
      Scalar Converges finiteDiagonal thermodynamic continuum)
    cutoff →
  LessEqual dataSet
    (Distance dataSet continuum (finiteDiagonal cutoff))
    (combinedTail dataSet cutoff)
continuumToFiniteDiagonal dataSet cutoff =
  transitive dataSet
    (distanceSymmetric dataSet continuum (finiteDiagonal cutoff))
    (finiteDiagonalToContinuum dataSet cutoff)

diagonalDifferenceBelowTwoCombinedTails :
  ∀ {Scalar Converges finiteDiagonal thermodynamic continuum}
    (dataSet : StagedDiagonalTailData
      Scalar Converges finiteDiagonal thermodynamic continuum)
    left right →
  LessEqual dataSet
    (Distance dataSet (finiteDiagonal left) (finiteDiagonal right))
    (add dataSet (combinedTail dataSet left) (combinedTail dataSet right))
diagonalDifferenceBelowTwoCombinedTails dataSet left right =
  transitive dataSet
    (distanceTriangle dataSet
      (finiteDiagonal left) continuum (finiteDiagonal right))
    (addMonotone dataSet
      (finiteDiagonalToContinuum dataSet left)
      (continuumToFiniteDiagonal dataSet right))

diagonalDifferenceBelowEarlierTail :
  ∀ {Scalar Converges finiteDiagonal thermodynamic continuum}
    (dataSet : StagedDiagonalTailData
      Scalar Converges finiteDiagonal thermodynamic continuum)
    left right →
  LessEqual dataSet
    (Distance dataSet (finiteDiagonal left) (finiteDiagonal right))
    (doubledCombinedTail dataSet (earlier dataSet left right))
diagonalDifferenceBelowEarlierTail dataSet left right =
  transitive dataSet
    (diagonalDifferenceBelowTwoCombinedTails dataSet left right)
    (addMonotone dataSet
      (combinedTailAntitoneLeft dataSet left right)
      (combinedTailAntitoneRight dataSet left right))

stagedTailsGiveDiagonalTail :
  ∀ {Scalar Converges finiteDiagonal thermodynamic continuum} →
  (dataSet : StagedDiagonalTailData
    Scalar Converges finiteDiagonal thermodynamic continuum) →
  Thermo.TailControlledConvergence
    Scalar Converges finiteDiagonal continuum
stagedTailsGiveDiagonalTail dataSet = record
  { Thermo.TailControlledConvergence.Distance = Distance dataSet
  ; Thermo.TailControlledConvergence.Tail = doubledCombinedTail dataSet
  ; Thermo.TailControlledConvergence.LessEqual = LessEqual dataSet
  ; Thermo.TailControlledConvergence.earlier = earlier dataSet
  ; Thermo.TailControlledConvergence.differenceControlled =
      diagonalDifferenceBelowEarlierTail dataSet
  ; Thermo.TailControlledConvergence.tailVanishes =
      doubledCombinedTailVanishes dataSet
  ; Thermo.TailControlledConvergence.cauchyCompletionFromTail =
      cauchyCompletionFromTail dataSet
  }

stagedDiagonalSequenceConverges :
  ∀ {Scalar Converges finiteDiagonal thermodynamic continuum}
    (dataSet : StagedDiagonalTailData
      Scalar Converges finiteDiagonal thermodynamic continuum) →
  Converges finiteDiagonal continuum
stagedDiagonalSequenceConverges dataSet =
  Thermo.tailControlledSequenceConverges
    (stagedTailsGiveDiagonalTail dataSet)

stagedFiniteToContinuumTriangleLevel : ProofLevel
stagedFiniteToContinuumTriangleLevel = machineChecked

stagedDiagonalCauchyLevel : ProofLevel
stagedDiagonalCauchyLevel = machineChecked

stagedDiagonalConvergenceLevel : ProofLevel
stagedDiagonalConvergenceLevel = machineChecked
