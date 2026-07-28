module DASHI.Physics.Closure.NSTriadKNG3ShellIndexPartition where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Jean-Michel Bony; Hajer Bahouri; Jean-Yves Chemin; Raphael
-- Danchin; Terence Tao; DASHI repository contributors.
-- Title: "Decidable and exhaustive G=3 partition of three dyadic shell
-- indices".
-- Venue/year: Annales scientifiques de l'Ecole Normale Superieure 14 (1981);
-- Fourier Analysis and Nonlinear Partial Differential Equations, Springer,
-- 2011; UCLA Math 247B lecture notes, 2007; DASHI formal development, 2026.
-- DOI: 10.24033/asens.1404; 10.1007/978-3-642-16830-7; Tao's lecture notes
-- and the repository-original exact classifier have no DOI.
-- Uses: the canonical left/right/output-low predicates at gap three,
-- pairwise width one, pairwise width two, and decidability of natural order.
-- Relationship: proves an exact shell-index partition independently of the
-- Fourier-mode owner.  The remaining repository bridge must show that every
-- retained nonzero resonant mode has an owned shell and that cutoff/orbit/
-- helicity operations preserve that owner.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)
import Data.Nat.Properties as Nat
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)

import DASHI.Physics.Closure.NSTriadKNExactDyadicShellGeometry as Geometry

leftLow? : ∀ left right output → Dec (Geometry.LeftLow left right output)
leftLow? left right output
  with Nat._≤?_ (left + Geometry.farGap) right
     | Nat._≤?_ (left + Geometry.farGap) output
... | yes belowRight | yes belowOutput =
  yes (Geometry.left-low belowRight belowOutput)
... | no notBelowRight | _ =
  no (λ evidence →
    notBelowRight (Geometry.LeftLow.belowRight evidence))
... | _ | no notBelowOutput =
  no (λ evidence →
    notBelowOutput (Geometry.LeftLow.belowOutput evidence))

rightLow? : ∀ left right output → Dec (Geometry.RightLow left right output)
rightLow? left right output
  with Nat._≤?_ (right + Geometry.farGap) left
     | Nat._≤?_ (right + Geometry.farGap) output
... | yes belowLeft | yes belowOutput =
  yes (Geometry.right-low belowLeft belowOutput)
... | no notBelowLeft | _ =
  no (λ evidence →
    notBelowLeft (Geometry.RightLow.belowLeft evidence))
... | _ | no notBelowOutput =
  no (λ evidence →
    notBelowOutput (Geometry.RightLow.belowOutput evidence))

outputLow? : ∀ left right output → Dec (Geometry.OutputLow left right output)
outputLow? left right output
  with Nat._≤?_ (output + Geometry.farGap) left
     | Nat._≤?_ (output + Geometry.farGap) right
... | yes belowLeft | yes belowRight =
  yes (Geometry.output-low belowLeft belowRight)
... | no notBelowLeft | _ =
  no (λ evidence →
    notBelowLeft (Geometry.OutputLow.belowLeft evidence))
... | _ | no notBelowRight =
  no (λ evidence →
    notBelowRight (Geometry.OutputLow.belowRight evidence))

withinOne? :
  ∀ left right output →
  Dec (Geometry.PairwiseWithinOne left right output)
withinOne? left right output
  with Nat._≤?_ left (right + Geometry.nearWidth)
     | Nat._≤?_ right (left + Geometry.nearWidth)
     | Nat._≤?_ left (output + Geometry.nearWidth)
     | Nat._≤?_ output (left + Geometry.nearWidth)
     | Nat._≤?_ right (output + Geometry.nearWidth)
     | Nat._≤?_ output (right + Geometry.nearWidth)
... | yes lr | yes rl | yes lo | yes ol | yes ro | yes or =
  yes (Geometry.within-one lr rl lo ol ro or)
... | no n | _ | _ | _ | _ | _ =
  no (λ evidence → n (Geometry.PairwiseWithinOne.leftBelowRight evidence))
... | _ | no n | _ | _ | _ | _ =
  no (λ evidence → n (Geometry.PairwiseWithinOne.rightBelowLeft evidence))
... | _ | _ | no n | _ | _ | _ =
  no (λ evidence → n (Geometry.PairwiseWithinOne.leftBelowOutput evidence))
... | _ | _ | _ | no n | _ | _ =
  no (λ evidence → n (Geometry.PairwiseWithinOne.outputBelowLeft evidence))
... | _ | _ | _ | _ | no n | _ =
  no (λ evidence → n (Geometry.PairwiseWithinOne.rightBelowOutput evidence))
... | _ | _ | _ | _ | _ | no n =
  no (λ evidence → n (Geometry.PairwiseWithinOne.outputBelowRight evidence))

withinTwo? :
  ∀ left right output →
  Dec (Geometry.PairwiseWithinTwo left right output)
withinTwo? left right output
  with Nat._≤?_ left (right + Geometry.transitionSpan)
     | Nat._≤?_ right (left + Geometry.transitionSpan)
     | Nat._≤?_ left (output + Geometry.transitionSpan)
     | Nat._≤?_ output (left + Geometry.transitionSpan)
     | Nat._≤?_ right (output + Geometry.transitionSpan)
     | Nat._≤?_ output (right + Geometry.transitionSpan)
... | yes lr | yes rl | yes lo | yes ol | yes ro | yes or =
  yes (Geometry.within-two lr rl lo ol ro or)
... | no n | _ | _ | _ | _ | _ =
  no (λ evidence → n (Geometry.PairwiseWithinTwo.leftBelowRight evidence))
... | _ | no n | _ | _ | _ | _ =
  no (λ evidence → n (Geometry.PairwiseWithinTwo.rightBelowLeft evidence))
... | _ | _ | no n | _ | _ | _ =
  no (λ evidence → n (Geometry.PairwiseWithinTwo.leftBelowOutput evidence))
... | _ | _ | _ | no n | _ | _ =
  no (λ evidence → n (Geometry.PairwiseWithinTwo.outputBelowLeft evidence))
... | _ | _ | _ | _ | no n | _ =
  no (λ evidence → n (Geometry.PairwiseWithinTwo.rightBelowOutput evidence))
... | _ | _ | _ | _ | _ | no n =
  no (λ evidence → n (Geometry.PairwiseWithinTwo.outputBelowRight evidence))

data G3ShellCase (left right output : Nat) : Set where
  leftSeparated :
    Geometry.LeftLow left right output →
    G3ShellCase left right output

  rightSeparated :
    (Geometry.LeftLow left right output → ⊥) →
    Geometry.RightLow left right output →
    G3ShellCase left right output

  outputSeparated :
    (Geometry.LeftLow left right output → ⊥) →
    (Geometry.RightLow left right output → ⊥) →
    Geometry.OutputLow left right output →
    G3ShellCase left right output

  comparable :
    (Geometry.LeftLow left right output → ⊥) →
    (Geometry.RightLow left right output → ⊥) →
    (Geometry.OutputLow left right output → ⊥) →
    Geometry.PairwiseWithinOne left right output →
    G3ShellCase left right output

  transition :
    (Geometry.LeftLow left right output → ⊥) →
    (Geometry.RightLow left right output → ⊥) →
    (Geometry.OutputLow left right output → ⊥) →
    (Geometry.PairwiseWithinOne left right output → ⊥) →
    Geometry.PairwiseWithinTwo left right output →
    G3ShellCase left right output

  residual :
    (Geometry.LeftLow left right output → ⊥) →
    (Geometry.RightLow left right output → ⊥) →
    (Geometry.OutputLow left right output → ⊥) →
    (Geometry.PairwiseWithinOne left right output → ⊥) →
    (Geometry.PairwiseWithinTwo left right output → ⊥) →
    G3ShellCase left right output

classifyG3Shells : ∀ left right output → G3ShellCase left right output
classifyG3Shells left right output
  with leftLow? left right output
... | yes leftEvidence = leftSeparated leftEvidence
... | no notLeft with rightLow? left right output
...   | yes rightEvidence = rightSeparated notLeft rightEvidence
...   | no notRight with outputLow? left right output
...     | yes outputEvidence = outputSeparated notLeft notRight outputEvidence
...     | no notOutput with withinOne? left right output
...       | yes nearEvidence = comparable notLeft notRight notOutput nearEvidence
...       | no notNear with withinTwo? left right output
...         | yes transitionEvidence =
              transition notLeft notRight notOutput notNear transitionEvidence
...         | no notTransition =
              residual notLeft notRight notOutput notNear notTransition

G3ShellIndexPartitionTotal : Set
G3ShellIndexPartitionTotal = ∀ left right output → G3ShellCase left right output

G3ShellIndexPartitionTotalProof : G3ShellIndexPartitionTotal
G3ShellIndexPartitionTotalProof = classifyG3Shells

G3ShellIndexPartitionClosed : Bool
G3ShellIndexPartitionClosed = true

G3ShellIndexPartitionClosedIsTrue : G3ShellIndexPartitionClosed ≡ true
G3ShellIndexPartitionClosedIsTrue = refl

repositoryModeToShellOwnerBridgeStillRequired : Bool
repositoryModeToShellOwnerBridgeStillRequired = true

repositoryModeToShellOwnerBridgeStillRequiredIsTrue :
  repositoryModeToShellOwnerBridgeStillRequired ≡ true
repositoryModeToShellOwnerBridgeStillRequiredIsTrue = refl
