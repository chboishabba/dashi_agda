module DASHI.Physics.YangMills.BalabanPeriodicPatchGreenTransferRegression where

open import Agda.Builtin.Equality using (refl)

import DASHI.Physics.YangMills.BalabanPeriodicFourierHodgeRegression as Base
import DASHI.Physics.YangMills.BalabanPeriodicPhysicalClosureRegression as Physical
import DASHI.Physics.YangMills.BalabanPeriodicBulkHessianGreenClosure as Bulk
import DASHI.Physics.YangMills.BalabanPeriodicPatchGreenTransfer as Transfer

certificate : Bulk.PeriodicBulkHessianGreenCertificate
  Base.One Base.One Base.One Base.One
certificate = Physical.bulkGreenCertificate

greenTransfer :
  Transfer.PhysicalPatchOperatorTransfer
    Base.One Base.One Base.One Base.One Base.One
    certificate Base.one
    (Bulk.green certificate Base.one) (Bulk.CG certificate)
greenTransfer = record
  { Transfer.extension = λ patch → Base.one
  ; Transfer.restriction = λ bulk → Base.one
  ; Transfer.patchNorm = λ patch → Base.one
  ; Transfer.CE = Base.one
  ; Transfer.CR = Base.one
  ; Transfer.Cpatch = Base.one
  ; Transfer.restrictionAfterExtension = λ patch → refl
  ; Transfer.extensionNormBound = λ patch → Base.holds
  ; Transfer.restrictionNormBound = λ bulk → Base.holds
  ; Transfer.patchOperator = λ patch → Base.one
  ; Transfer.operatorTransferIdentity = λ patch → refl
  ; Transfer.lessEqualTransitive = λ left≤middle middle≤right → Base.holds
  ; Transfer.equalityLeft = λ equality below → Base.holds
  ; Transfer.multiplyMonotoneLeft = λ constant below → Base.holds
  ; Transfer.bulkOperatorBound = Bulk.weightedGreenBound certificate Base.one
  ; Transfer.constantTransport = λ patch → Base.holds
  }

gradientTransfer :
  Transfer.PhysicalPatchOperatorTransfer
    Base.One Base.One Base.One Base.One Base.One
    certificate Base.one
    (Bulk.gradientGreen certificate Base.one) (Bulk.CGradG certificate)
gradientTransfer = record
  { Transfer.extension = λ patch → Base.one
  ; Transfer.restriction = λ bulk → Base.one
  ; Transfer.patchNorm = λ patch → Base.one
  ; Transfer.CE = Base.one
  ; Transfer.CR = Base.one
  ; Transfer.Cpatch = Base.one
  ; Transfer.restrictionAfterExtension = λ patch → refl
  ; Transfer.extensionNormBound = λ patch → Base.holds
  ; Transfer.restrictionNormBound = λ bulk → Base.holds
  ; Transfer.patchOperator = λ patch → Base.one
  ; Transfer.operatorTransferIdentity = λ patch → refl
  ; Transfer.lessEqualTransitive = λ left≤middle middle≤right → Base.holds
  ; Transfer.equalityLeft = λ equality below → Base.holds
  ; Transfer.multiplyMonotoneLeft = λ constant below → Base.holds
  ; Transfer.bulkOperatorBound = Bulk.weightedGradientGreenBound certificate Base.one
  ; Transfer.constantTransport = λ patch → Base.holds
  }

secondGradientTransfer :
  Transfer.PhysicalPatchOperatorTransfer
    Base.One Base.One Base.One Base.One Base.One
    certificate Base.one
    (Bulk.secondGradientGreen certificate Base.one)
    (Bulk.CSecondGradG certificate)
secondGradientTransfer = record
  { Transfer.extension = λ patch → Base.one
  ; Transfer.restriction = λ bulk → Base.one
  ; Transfer.patchNorm = λ patch → Base.one
  ; Transfer.CE = Base.one
  ; Transfer.CR = Base.one
  ; Transfer.Cpatch = Base.one
  ; Transfer.restrictionAfterExtension = λ patch → refl
  ; Transfer.extensionNormBound = λ patch → Base.holds
  ; Transfer.restrictionNormBound = λ bulk → Base.holds
  ; Transfer.patchOperator = λ patch → Base.one
  ; Transfer.operatorTransferIdentity = λ patch → refl
  ; Transfer.lessEqualTransitive = λ left≤middle middle≤right → Base.holds
  ; Transfer.equalityLeft = λ equality below → Base.holds
  ; Transfer.multiplyMonotoneLeft = λ constant below → Base.holds
  ; Transfer.bulkOperatorBound =
      Bulk.weightedSecondGradientGreenBound certificate Base.one
  ; Transfer.constantTransport = λ patch → Base.holds
  }

tripleTransfer :
  Transfer.PhysicalPatchTripleTransfer
    Base.One Base.One Base.One Base.One Base.One certificate Base.one
tripleTransfer = record
  { Transfer.greenTransfer = greenTransfer
  ; Transfer.gradientGreenTransfer = gradientTransfer
  ; Transfer.secondGradientGreenTransfer = secondGradientTransfer
  }

tripleBounds :
  Transfer.PhysicalPatchTripleBounds
    Base.One Base.One Base.One Base.One Base.One certificate Base.one tripleTransfer
tripleBounds = Transfer.assemblePhysicalPatchTripleBounds tripleTransfer

boundaryGreenRegression : Base.Holds
boundaryGreenRegression =
  Transfer.PhysicalPatchTripleBounds.greenBound tripleBounds Base.one

fourRegimeFamily :
  Transfer.FourPhysicalPatchTransferFamily
    Base.One Base.One Base.One Base.One
    Base.One Base.One Base.One Base.One certificate Base.one
fourRegimeFamily = record
  { Transfer.boundary = tripleTransfer
  ; Transfer.interface = tripleTransfer
  ; Transfer.corner = tripleTransfer
  ; Transfer.nested = tripleTransfer
  }
