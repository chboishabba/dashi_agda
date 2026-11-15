module DASHI.Foundations.BalancedTernaryC3OppositionGrokkingBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Foundations.BalancedTernaryStageSymmetryExact as Ternary
import DASHI.Cognition.PNF.ModularFourierGrokkingC3Exact as Grok
import DASHI.Cognition.PNF.GrokkingEquivarianceDefectGeometryExact as Defect
import DASHI.Reasoning.TrialecticBoundaryFaceNonfactorabilityExact as Face
import DASHI.Core.ArgumentResponseNonGeometricOppositeBidiExact as Argument

-- A balanced triad has three coordinate positions. The cyclic *action*
-- on these positions is different from choosing one of three digit values.
-- No assertion is made that this action is a semantic argument negation or
-- an empirical learned neural representation.

Pattern : Set
Pattern = Ternary.TriadPattern

rotate : Pattern → Pattern
rotate (Ternary.triad a b c) = Ternary.triad b c a

reflect : Pattern → Pattern
reflect (Ternary.triad a b c) = Ternary.triad a c b

rotateTwice : Pattern → Pattern
rotateTwice x = rotate (rotate x)

rotationCubedIdentity : (x : Pattern) →
  rotate (rotateTwice x) ≡ x
rotationCubedIdentity (Ternary.triad a b c) = refl

reflectionSquaredIdentity : (x : Pattern) →
  reflect (reflect x) ≡ x
reflectionSquaredIdentity (Ternary.triad a b c) = refl

reflectionConjugatesRotationToInverse : (x : Pattern) →
  reflect (rotate (reflect x)) ≡ rotateTwice x
reflectionConjugatesRotationToInverse (Ternary.triad a b c) = refl

-- Componentwise sign inversion commutes with rotation.  This is the
-- central C2 x C3 action relevant to antipodal signed-source routing.
-- It cannot serve as the S3 conjugating reflection above.

antipodalCommutesWithRotation : (x : Pattern) →
  rotate (Ternary.strictInverse x)
  ≡ Ternary.strictInverse (rotate x)
antipodalCommutesWithRotation (Ternary.triad a b c) = refl

antipodalCommutesWithReflection : (x : Pattern) →
  reflect (Ternary.strictInverse x)
  ≡ Ternary.strictInverse (reflect x)
antipodalCommutesWithReflection (Ternary.triad a b c) = refl

-- The balanced-zero scalar projection loses shape. This example has
-- equal positive/negative counts but is not an all-zero pattern.

nontrivialBalancedZero : Pattern
nontrivialBalancedZero =
  Ternary.triad Ternary.pos Ternary.neg Ternary.zeroDigit

allOpen : Pattern
allOpen = Ternary.allOpen

balancedZeroHasDifferentPattern : nontrivialBalancedZero ≡ allOpen → ⊥
balancedZeroHasDifferentPattern ()

-- Source-specific proof donors: on the finite C3 task the character law
-- generalises to p22 whereas a memorizer fits the other eight pairs;
-- the directed task-equivariance defect is strictly smaller for the
-- character rule. These are *reused theorems*, not empirical claims.

grokkingMemorizerFitsDeclaredTraining :
  Grok.TrainingEquivalent Grok.memorizerRule Grok.algorithmicRule
grokkingMemorizerFitsDeclaredTraining =
  Grok.memorizerAndAlgorithmTrainingEquivalent

grokkingMemorizerFailsHeldout :
  Grok.FullTaskEquivalent Grok.memorizerRule Grok.algorithmicRule → ⊥
grokkingMemorizerFailsHeldout =
  Grok.memorizerAndAlgorithmNotFullTaskEquivalent

grokkingCharacterHasZeroActionDefect :
  Defect.equivarianceDefect Grok.algorithmicRule ≡ 0
grokkingCharacterHasZeroActionDefect =
  Defect.algorithmicEquivarianceDefectIsZero

grokkingMemorizerHasTwoActionDefects :
  Defect.equivarianceDefect Grok.memorizerRule ≡ 2
grokkingMemorizerHasTwoActionDefects =
  Defect.memorizerEquivarianceDefectIsTwo

-- The boundary edges do not determine the triadic face. Reuse the exact
-- no-factorisation proof rather than interpreting signed scalar zero
-- as semantic mediation, contradiction or absence.

threeEdgesCannotDetermineFace :
  Face.ThreeDyadsDetermineTrialectic → ⊥
threeEdgesCannotDetermineFace =
  Face.threeDyadsDoNotDetermineTrialectic

counterargumentIsNotAutomaticallyGeometricAntipode :
  Argument.AlternativeExplanationIsGeometricAntipode → ⊥
counterargumentIsNotAutomaticallyGeometricAntipode =
  Argument.alternativeExplanationIsNotGeometricAntipode
