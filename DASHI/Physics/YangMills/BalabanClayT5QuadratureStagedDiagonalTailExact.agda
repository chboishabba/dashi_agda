module DASHI.Physics.YangMills.BalabanClayT5QuadratureStagedDiagonalTailExact where

------------------------------------------------------------------------
-- THREE-STAGE DIAGONAL CONVERGENCE
--
--   quadrature_n
--      -> literal finite-volume/Haar expectation
--      -> thermodynamic expectation
--      -> continuum expectation.
--
-- This is the corrected downstream consumer for finite rational Gate4
-- quadratures.  No exact equality between one quadrature and the literal Haar
-- measure is required.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as Thermo

record QuadratureStagedDiagonalTailData
    (Scalar : Set)
    (Converges : (Nat → Scalar) → Scalar → Set)
    (quadratureDiagonal finiteDiagonal thermodynamic : Nat → Scalar)
    (continuum : Scalar) : Set₁ where
  field
    Distance : Scalar → Scalar → Scalar
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

    quadratureTail volumeTail cutoffTail : Nat → Scalar

    quadratureToFinite : ∀ cutoff →
      LessEqual
        (Distance (quadratureDiagonal cutoff) (finiteDiagonal cutoff))
        (quadratureTail cutoff)

    finiteToThermodynamic : ∀ cutoff →
      LessEqual
        (Distance (finiteDiagonal cutoff) (thermodynamic cutoff))
        (volumeTail cutoff)

    thermodynamicToContinuum : ∀ cutoff →
      LessEqual
        (Distance (thermodynamic cutoff) continuum)
        (cutoffTail cutoff)

    earlier : Nat → Nat → Nat

    quadratureTailAntitoneLeft : ∀ left right →
      LessEqual (quadratureTail left)
        (quadratureTail (earlier left right))
    quadratureTailAntitoneRight : ∀ left right →
      LessEqual (quadratureTail right)
        (quadratureTail (earlier left right))

    volumeTailAntitoneLeft : ∀ left right →
      LessEqual (volumeTail left)
        (volumeTail (earlier left right))
    volumeTailAntitoneRight : ∀ left right →
      LessEqual (volumeTail right)
        (volumeTail (earlier left right))

    cutoffTailAntitoneLeft : ∀ left right →
      LessEqual (cutoffTail left)
        (cutoffTail (earlier left right))
    cutoffTailAntitoneRight : ∀ left right →
      LessEqual (cutoffTail right)
        (cutoffTail (earlier left right))

    doubledCombinedTailVanishes : Set

    cauchyCompletionFromTail :
      (∀ left right →
        LessEqual
          (Distance
            (quadratureDiagonal left)
            (quadratureDiagonal right))
          (doubledCombinedTailAt (earlier left right))) →
      doubledCombinedTailVanishes →
      Converges quadratureDiagonal continuum

  combinedTailAt : Nat → Scalar
  combinedTailAt cutoff =
    add (quadratureTail cutoff)
      (add (volumeTail cutoff) (cutoffTail cutoff))

  doubledCombinedTailAt : Nat → Scalar
  doubledCombinedTailAt cutoff =
    add (combinedTailAt cutoff) (combinedTailAt cutoff)

open QuadratureStagedDiagonalTailData public

quadratureToContinuum :
  ∀ {Scalar Converges quadratureDiagonal finiteDiagonal thermodynamic continuum}
    (dataSet :
      QuadratureStagedDiagonalTailData
        Scalar Converges
        quadratureDiagonal finiteDiagonal thermodynamic continuum)
    cutoff →
  LessEqual dataSet
    (Distance dataSet (quadratureDiagonal cutoff) continuum)
    (combinedTailAt dataSet cutoff)
quadratureToContinuum dataSet cutoff =
  transitive dataSet
    (distanceTriangle dataSet
      (quadratureDiagonal cutoff)
      (finiteDiagonal cutoff)
      continuum)
    (addMonotone dataSet
      (quadratureToFinite dataSet cutoff)
      (transitive dataSet
        (distanceTriangle dataSet
          (finiteDiagonal cutoff)
          (thermodynamic cutoff)
          continuum)
        (addMonotone dataSet
          (finiteToThermodynamic dataSet cutoff)
          (thermodynamicToContinuum dataSet cutoff))))

continuumToQuadrature :
  ∀ {Scalar Converges quadratureDiagonal finiteDiagonal thermodynamic continuum}
    (dataSet :
      QuadratureStagedDiagonalTailData
        Scalar Converges
        quadratureDiagonal finiteDiagonal thermodynamic continuum)
    cutoff →
  LessEqual dataSet
    (Distance dataSet continuum (quadratureDiagonal cutoff))
    (combinedTailAt dataSet cutoff)
continuumToQuadrature dataSet cutoff =
  transitive dataSet
    (distanceSymmetric dataSet continuum (quadratureDiagonal cutoff))
    (quadratureToContinuum dataSet cutoff)

combinedTailAntitoneLeft :
  ∀ {Scalar Converges quadratureDiagonal finiteDiagonal thermodynamic continuum}
    (dataSet :
      QuadratureStagedDiagonalTailData
        Scalar Converges
        quadratureDiagonal finiteDiagonal thermodynamic continuum)
    left right →
  LessEqual dataSet
    (combinedTailAt dataSet left)
    (combinedTailAt dataSet (earlier dataSet left right))
combinedTailAntitoneLeft dataSet left right =
  addMonotone dataSet
    (quadratureTailAntitoneLeft dataSet left right)
    (addMonotone dataSet
      (volumeTailAntitoneLeft dataSet left right)
      (cutoffTailAntitoneLeft dataSet left right))

combinedTailAntitoneRight :
  ∀ {Scalar Converges quadratureDiagonal finiteDiagonal thermodynamic continuum}
    (dataSet :
      QuadratureStagedDiagonalTailData
        Scalar Converges
        quadratureDiagonal finiteDiagonal thermodynamic continuum)
    left right →
  LessEqual dataSet
    (combinedTailAt dataSet right)
    (combinedTailAt dataSet (earlier dataSet left right))
combinedTailAntitoneRight dataSet left right =
  addMonotone dataSet
    (quadratureTailAntitoneRight dataSet left right)
    (addMonotone dataSet
      (volumeTailAntitoneRight dataSet left right)
      (cutoffTailAntitoneRight dataSet left right))

quadratureDifferenceBelowEarlierTail :
  ∀ {Scalar Converges quadratureDiagonal finiteDiagonal thermodynamic continuum}
    (dataSet :
      QuadratureStagedDiagonalTailData
        Scalar Converges
        quadratureDiagonal finiteDiagonal thermodynamic continuum)
    left right →
  LessEqual dataSet
    (Distance dataSet
      (quadratureDiagonal left)
      (quadratureDiagonal right))
    (doubledCombinedTailAt dataSet (earlier dataSet left right))
quadratureDifferenceBelowEarlierTail dataSet left right =
  transitive dataSet
    (distanceTriangle dataSet
      (quadratureDiagonal left)
      continuum
      (quadratureDiagonal right))
    (addMonotone dataSet
      (transitive dataSet
        (quadratureToContinuum dataSet left)
        (combinedTailAntitoneLeft dataSet left right))
      (transitive dataSet
        (continuumToQuadrature dataSet right)
        (combinedTailAntitoneRight dataSet left right)))

quadratureStagedTailControlledConvergence :
  ∀ {Scalar Converges quadratureDiagonal finiteDiagonal thermodynamic continuum}
    (dataSet :
      QuadratureStagedDiagonalTailData
        Scalar Converges
        quadratureDiagonal finiteDiagonal thermodynamic continuum) →
  Thermo.TailControlledConvergence
    Scalar Converges quadratureDiagonal continuum
quadratureStagedTailControlledConvergence dataSet = record
  { Thermo.TailControlledConvergence.Distance =
      Distance dataSet
  ; Thermo.TailControlledConvergence.Tail =
      doubledCombinedTailAt dataSet
  ; Thermo.TailControlledConvergence.LessEqual =
      LessEqual dataSet
  ; Thermo.TailControlledConvergence.earlier =
      earlier dataSet
  ; Thermo.TailControlledConvergence.differenceControlled =
      quadratureDifferenceBelowEarlierTail dataSet
  ; Thermo.TailControlledConvergence.tailVanishes =
      doubledCombinedTailVanishes dataSet
  ; Thermo.TailControlledConvergence.cauchyCompletionFromTail =
      cauchyCompletionFromTail dataSet
  }

quadratureDiagonalConvergesToContinuum :
  ∀ {Scalar Converges quadratureDiagonal finiteDiagonal thermodynamic continuum}
    (dataSet :
      QuadratureStagedDiagonalTailData
        Scalar Converges
        quadratureDiagonal finiteDiagonal thermodynamic continuum) →
  Converges quadratureDiagonal continuum
quadratureDiagonalConvergesToContinuum dataSet =
  Thermo.tailControlledSequenceConverges
    (quadratureStagedTailControlledConvergence dataSet)

quadratureFiniteContinuumTriangleLevel : ProofLevel
quadratureFiniteContinuumTriangleLevel = machineChecked

quadratureStagedDiagonalCauchyLevel : ProofLevel
quadratureStagedDiagonalCauchyLevel = machineChecked

quadratureStagedDiagonalConvergenceLevel : ProofLevel
quadratureStagedDiagonalConvergenceLevel = machineChecked
