module DASHI.Physics.Closure.UnifiedPhysicsTheorem where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.PhysicsClosureTheoremChecklist as PCTC
open import DASHI.Physics.Closure.PhysicsClosureFivePillarsTheorem as PC5
open import DASHI.Physics.Closure.PhysicsClosureFull as PCF
open import DASHI.Physics.Closure.PhysicsClosureFullInstance as PCFI
open import DASHI.Physics.Closure.PhysicsClosureFullCanonicalBridgePackage as PCBP
open import DASHI.Physics.Closure.CanonicalToNoncanonicalCoarseRecoveryIdentification as CNCRI
open import DASHI.Physics.Closure.PhysicsUnificationToCanonicalClosureAdapter as PUCTCA
open import DASHI.Physics.ConcreteClosureStack as CCS
open import DASHI.Physics.UnifiedClosure as UC

record UnifiedPhysicsTheorem : Setω where
  field
    theoremChecklist : PCTC.PhysicsClosureTheoremChecklist
    headlineTheorem : PCTC.PhysicsClosureHeadlineTheorem
    namedTheoremChecklist : PCTC.PhysicsClosureNamedTheoremChecklist
    realizationIndependenceChecklist :
      PCTC.PhysicsClosureRealizationIndependenceChecklist
    fivePillarsTheorem : PC5.PhysicsClosureFivePillarsTheorem
    fullClosure : PCF.PhysicsClosureFull
    fullCanonicalBridgePackage : PCBP.PhysicsClosureFullCanonicalBridgePackage
    coarseRecoveryIdentification :
      CNCRI.CanonicalToNoncanonicalCoarseRecoveryIdentification
    unificationAdapter :
      PUCTCA.PhysicsUnificationToCanonicalClosureAdapter
    concreteUnification :
      UC.PhysicsUnification CCS.realStack

canonicalUnifiedPhysicsTheorem : UnifiedPhysicsTheorem
canonicalUnifiedPhysicsTheorem =
  record
    { theoremChecklist =
        PCTC.canonicalPhysicsClosureTheoremChecklist
    ; headlineTheorem =
        PCTC.canonicalPhysicsClosureHeadlineTheorem
    ; namedTheoremChecklist =
        PCTC.canonicalPhysicsClosureNamedTheoremChecklist
    ; realizationIndependenceChecklist =
        PCTC.b4PhysicsClosureRealizationIndependenceChecklist
    ; fivePillarsTheorem =
        PC5.canonicalPhysicsClosureFivePillarsTheorem
    ; fullClosure =
        PCFI.physicsClosureFull
    ; fullCanonicalBridgePackage =
        PCBP.canonicalPhysicsClosureFullCanonicalBridgePackage
    ; coarseRecoveryIdentification =
        CNCRI.canonicalToNoncanonicalCoarseRecoveryIdentification
    ; unificationAdapter =
        PUCTCA.canonicalPhysicsUnificationToCanonicalClosureAdapter
    ; concreteUnification =
        CCS.physicsUnification
    }
