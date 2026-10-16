module DASHI.Moonshine.JackDanielsSmallPrimeJCoarseFineTerminalMaxCutExact where

------------------------------------------------------------------------
-- JACK DANIEL'S p=2,3 TERMINAL MAX-CUT WITH jCOARSE/jFINE GOVERNANCE
--
-- ATTRIBUTION / CLAIM BOUNDARY
--
-- This owner only composes theorem/status owners already in-repo.
--
-- External authority remains explicitly separated:
--   * Ogg / Duncan--Ono: supersingular-prime and Jack-Daniels context;
--   * Duncan--Swisher: monstrous-exponent arithmetic upstream;
--   * Aricheta: off-diagonal p ∤ N supersingular-level <-> Monster-centralizer
--     Fricke theorem and the explicitly open p | N extension question;
--   * Katz--Mazur / Igusa theory and Kobin--Zureick-Brown: bad-level/wild
--     modular geometry;
--   * Carnahan / Dong--Li--Mason: twisted-module centralizer action and
--     generalized-moonshine modular-function precedent.
--
-- DASHI owns the typed synthesis below: jCoarse/jFine governs information loss,
-- the independent p=2,3 residual/groupoid machinery localises the finite
-- recognition problem, and the first genuinely source-external theorem wall is
-- the SAME bad-level object connecting supersingular/Igusa geometry to
-- Monster-centralizer/Fricke data (plus its corrected local valuation).
--
-- No source is credited with Base369 labels, and no finite j chart is promoted
-- to a literal modular curve or Monster object.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Moonshine.JackDanielsJCoarseFineNaturalRecognitionExact as JCF
import DASHI.Moonshine.JackDanielsCoarseJFrickeSensitivityNoGoExact as CoarseNoGo
import DASHI.Moonshine.OggSSPArithmeticIndependent369FrontierExact as Small
import DASHI.Moonshine.OggSSPSmallPrimeArichetaBadLevelDiagonalCutsetExact as Aricheta
import DASHI.Moonshine.OggSSPSmallPrimeArichetaIgusaBadLevelExtensionExact as ArichetaIgusa
import DASHI.Moonshine.OggSSPSmallPrimeGeneralizedMoonshineCentralizerBridgeExact as GM

------------------------------------------------------------------------
-- 1. Reuse the exact paid governance surfaces.
------------------------------------------------------------------------

jCoarseFineBoundary : JCF.JackDanielsJCoarseFineBoundary
jCoarseFineBoundary = JCF.canonicalJackDanielsJCoarseFineBoundary

coarseJNoGoBoundary : CoarseNoGo.CoarseJFrickeSensitivityBoundary
coarseJNoGoBoundary = CoarseNoGo.canonicalCoarseJFrickeSensitivityBoundary

smallCharacteristicFrontier = Small.canonicalArithmeticIndependent369Frontier

arichetaDiagonalBoundary : Aricheta.ArichetaBadLevelDiagonalBoundary
arichetaDiagonalBoundary = Aricheta.canonicalArichetaBadLevelDiagonalBoundary

arichetaIgusaBoundary : ArichetaIgusa.ArichetaIgusaBadLevelExtensionBoundary
arichetaIgusaBoundary = ArichetaIgusa.canonicalArichetaIgusaBadLevelExtensionBoundary

generalizedMoonshineBoundary : GM.GeneralizedMoonshineCentralizerBridgeBoundary
generalizedMoonshineBoundary = GM.canonicalGeneralizedMoonshineCentralizerBridgeBoundary

------------------------------------------------------------------------
-- 2. Exact terminal source-facing target.
--
-- The two small-prime diagonal lanes must be solved by ONE same-object bridge,
-- not by separately matching a finite code, a centralizer valuation and an
-- Igusa statistic after the fact.  We therefore bundle the two already-defined
-- external-theorem-shaped payments without claiming an inhabitant.
------------------------------------------------------------------------

record SmallPrimeNaturalRecognitionTerminalAuthority : Set₁ where
  constructor small-prime-natural-recognition-terminal-authority
  field
    badLevelSameObject :
      ArichetaIgusa.ArichetaIgusaBadLevelExtensionAuthority

    generalizedMoonshineBridge :
      GM.GeneralizedMoonshineCentralizerModularBridge

    twistedTraceValuation :
      GM.SmallPrimeTwistedTraceValuationAuthority generalizedMoonshineBridge

    SameBadLevelTwistedObjectWitness : Set
    sameBadLevelTwistedObject : SameBadLevelTwistedObjectWitness

    JCoarseFineFinePointCompatibilityWitness : Set
    jCoarseFineFinePointCompatibility :
      JCoarseFineFinePointCompatibilityWitness

    ObserverFibreRetainedWitness : Set
    observerFibreRetained : ObserverFibreRetainedWitness

    Independent369RecognitionCompatibilityWitness : Set
    independent369RecognitionCompatibility :
      Independent369RecognitionCompatibilityWitness

open SmallPrimeNaturalRecognitionTerminalAuthority public

------------------------------------------------------------------------
-- 3. Consequence firewall: the already-paid finite pieces cannot manufacture
--    the source-facing bad-level authority.
------------------------------------------------------------------------

data JCoarseFineObserverCreatesBadLevelCentralizerTheorem : Set where
data Independent369RecognitionCreatesArichetaExtension : Set where
data GeneralizedMoonshineCreatesCorrectedTenTwoValuation : Set where
data MatchingTenTwoScalarsCreatesSameObjectBridge : Set where

jObserverDoesNotCreateBadLevelTheorem :
  JCoarseFineObserverCreatesBadLevelCentralizerTheorem -> ⊥
jObserverDoesNotCreateBadLevelTheorem ()

independent369DoesNotCreateArichetaExtension :
  Independent369RecognitionCreatesArichetaExtension -> ⊥
independent369DoesNotCreateArichetaExtension ()

generalizedMoonshineDoesNotCreateTenTwoValuation :
  GeneralizedMoonshineCreatesCorrectedTenTwoValuation -> ⊥
generalizedMoonshineDoesNotCreateTenTwoValuation ()

matchingScalarsDoNotCreateSameObjectBridge :
  MatchingTenTwoScalarsCreatesSameObjectBridge -> ⊥
matchingScalarsDoNotCreateSameObjectBridge ()

------------------------------------------------------------------------
-- 4. Machine-readable terminal cut.
------------------------------------------------------------------------

record SmallPrimeJCoarseFineTerminalBoundary : Set where
  constructor small-prime-jcoarse-jfine-terminal-boundary
  field
    jCoarseFineObserverAndFibreGovernancePaid : Bool
    coarseJFrickeSensitiveConsumerNoGoPaid : Bool
    p2p3Independent369RecognitionInfrastructurePaid : Bool
    generalizedMoonshineCommonObjectPrecedentSourced : Bool
    arichetaOffDiagonalBridgeSourced : Bool
    pEqualsLevelDiagonalExplicitlyExcludedBySource : Bool
    badLevelIgusaGeometryAvailableAsInput : Bool

    sameObjectArichetaIgusaExtensionPaid : Bool
    correctedTwistedTraceValuationPaid : Bool
    jCoarseFineMonsterFactorizationPaid : Bool
    terminalAuthorityInhabited : Bool

canonicalSmallPrimeJCoarseFineTerminalBoundary :
  SmallPrimeJCoarseFineTerminalBoundary
canonicalSmallPrimeJCoarseFineTerminalBoundary =
  small-prime-jcoarse-jfine-terminal-boundary
    true true true true true true true
    false false false false
