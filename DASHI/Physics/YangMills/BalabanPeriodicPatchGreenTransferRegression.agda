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
  { extension = λ patch → Base.one
  ; restriction = λ bulk → Base.one
  ; patchNorm = λ patch → Base.one
  ; CE = Base.one
  ; CR = Base.one
  ; Cpatch = Base.one
  ; restrictionAfterExtension = λ patch → refl
  ; extensionNormBound = λ patch → Base.holds
  ; restrictionNormBound = λ bulk → Base.holds
  ; patchOperator = λ patch → Base.one
  ; operatorTransferIdentity = λ patch → refl
  ; lessEqualTransitive = λ left≤middle middle≤right → Base.holds
  ; equalityLeft = λ equality below → Base.holds
  ; multiplyMonotoneLeft = λ constant below → Base.holds
  ; bulkOperatorBound = Bulk.weightedGreenBound certificate Base.one
  ; constantTransport = λ patch → Base.holds
  }

gradientTransfer :
  Transfer.PhysicalPatchOperatorTransfer
    Base.One Base.One Base.One Base.One Base.One
    certificate Base.one
    (Bulk.gradientGreen certificate Base.one) (Bulk.CGradG certificate)
gradientTransfer = record
  { extension = λ patch → Base.one
  ; restriction = λ bulk → Base.one
  ; patchNorm = λ patch → Base.one
  ; CE = Base.one
  ; CR = Base.one
  ; Cpatch = Base.one
  ; restrictionAfterExtension = λ patch → refl
  ; extensionNormBound = λ patch → Base.holds
  ; restrictionNormBound = λ bulk → Base.holds
  ; patchOperator = λ patch → Base.one
  ; operatorTransferIdentity = λ patch → refl
  ; lessEqualTransitive = λ left≤middle middle≤right → Base.holds
  ; equalityLeft = λ equality below → Base.holds
  ; multiplyMonotoneLeft = λ constant below → Base.holds
  ; bulkOperatorBound = Bulk.weightedGradientGreenBound certificate Base.one
  ; constantTransport = λ patch → Base.holds
  }

secondGradientTransfer :
  Transfer.PhysicalPatchOperatorTransfer
    Base.One Base.One Base.One Base.One Base.One
    certificate Base.one
    (Bulk.secondGradientGreen certificate Base.one)
    (Bulk.CSecondGradG certificate)
secondGradientTransfer = record
  { extension = λ patch → Base.one
  ; restriction = λ bulk → Base.one
  ; patchNorm = λ patch → Base.one
  ; CE = Base.one
  ; CR = Base.one
  ; Cpatch = Base.one
  ; restrictionAfterExtension = λ patch → refl
  ; extensionNormBound = λ patch → Base.holds
  ; restrictionNormBound = λ bulk → Base.holds
  ; patchOperator = λ patch → Base.one
  ; operatorTransferIdentity = λ patch → refl
  ; lessEqualTransitive = λ left≤middle middle≤right → Base.holds
  ; equalityLeft = λ equality below → Base.holds
  ; multiplyMonotoneLeft = λ constant below → Base.holds
  ; bulkOperatorBound =
      Bulk.weightedSecondGradientGreenBound certificate Base.one
  ; constantTransport = λ patch → Base.holds
  }

tripleTransfer :
  Transfer.PhysicalPatchTripleTransfer
    Base.One Base.One Base.One Base.One Base.One certificate Base.one
tripleTransfer = record
  { greenTransfer = greenTransfer
  ; gradientGreenTransfer = gradientTransfer
  ; secondGradientGreenTransfer = secondGradientTransfer
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
  { boundary = tripleTransfer
  ; interface = tripleTransfer
  ; corner = tripleTransfer
  ; nested = tripleTransfer
  }
