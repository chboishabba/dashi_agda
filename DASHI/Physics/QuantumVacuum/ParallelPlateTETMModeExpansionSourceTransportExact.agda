module DASHI.Physics.QuantumVacuum.ParallelPlateTETMModeExpansionSourceTransportExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.SourceBackedTheoremTransportBidiExact as Transport
import DASHI.Physics.QuantumVacuum.ParallelPlateTETMModeExpansionSourceAuthorityExact as Source

------------------------------------------------------------------------
-- CLASSICAL PARALLEL-PLATE TE/TM EXPANSION -> LOCAL MODE SPACE
------------------------------------------------------------------------

sourceClaim : Transport.SourceBackedClaim
sourceClaim = record
  { Transport.SourceClaim =
      Source.fieldsExpandedAsLinearCombinationOfModes
        Source.canonicalParallelPlateTETMModeExpansionAuthority
  ; Transport.sourceReceipt = tt
  ; Transport.sourceName =
      Source.sourceName Source.canonicalParallelPlateTETMModeExpansionAuthority
  ; Transport.sourceLocator =
      Source.sourceLocator Source.canonicalParallelPlateTETMModeExpansionAuthority
  ; Transport.reading =
      "MIT parallel-plate classical TE/TM mode-expansion authority."
  }

record LocalParallelPlateModeExpansionTarget : Set₁ where
  field
    LocalModeExpansion : Set

    samePerfectConductorBoundaryProblem : Set
    sameFieldCarrierOrCompletion : Set
    sameTransverseModeSemantics : Set
    sameLongitudinalIntegerIndex : Set
    sameTETMConvention : Set
    sameExceptionalZeroSectorConvention : Set

    SameMathematicalObject : Set
    sameMathematicalObjectEvidence : SameMathematicalObject

    sourceExpansionToLocal :
      Transport.SourceClaim sourceClaim →
      SameMathematicalObject →
      LocalModeExpansion

    reading : String

open LocalParallelPlateModeExpansionTarget public

asTransportTarget :
  LocalParallelPlateModeExpansionTarget →
  Transport.LocalTheoremTarget sourceClaim
asTransportTarget T = record
  { Transport.LocalClaim = LocalModeExpansion T
  ; Transport.sameMathematicalObject = SameMathematicalObject T
  ; Transport.sourceSemanticsToLocal = sourceExpansionToLocal T
  ; Transport.reading = reading T
  }

compileLocalParallelPlateModeExpansion :
  (T : LocalParallelPlateModeExpansionTarget) →
  LocalModeExpansion T
compileLocalParallelPlateModeExpansion T =
  Transport.transportSourceBackedTheorem
    sourceClaim
    (asTransportTarget T)
    (record
      { Transport.objectWeld = sameMathematicalObjectEvidence T
      })

record ReverseModeExpansionWeldObligations : Set where
  field
    samePerfectConductorTraceDomain : Set
    sameFiniteEnergyOrHilbertCompletion : Set
    sameTransverseContinuumLabels : Set
    sameLongitudinalIntegerModes : Set
    sameTETMDefinitions : Set
    sameZeroSectorCounting : Set

open ReverseModeExpansionWeldObligations public

data MatchingNpiOverAFormulaAutomaticallyIdentifiesModeSpaces : Set where

matchingQuantisationDoesNotIdentifyCompletions :
  MatchingNpiOverAFormulaAutomaticallyIdentifiesModeSpaces → ⊥
matchingQuantisationDoesNotIdentifyCompletions ()

record Status : Set where
  field
    classicalVectorModeExpansionSourceBacked : Bool
    sourceTransportCompilerOwned : Bool
    localCasimirCarrierWeldClosed : Bool

    classicalVectorModeExpansionSourceBackedIsTrue :
      classicalVectorModeExpansionSourceBacked ≡ true
    sourceTransportCompilerOwnedIsTrue : sourceTransportCompilerOwned ≡ true
    localCasimirCarrierWeldClosedIsFalse : localCasimirCarrierWeldClosed ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { classicalVectorModeExpansionSourceBacked = true
  ; sourceTransportCompilerOwned = true
  ; localCasimirCarrierWeldClosed = false
  ; classicalVectorModeExpansionSourceBackedIsTrue = refl
  ; sourceTransportCompilerOwnedIsTrue = refl
  ; localCasimirCarrierWeldClosedIsFalse = refl
  }
