module DASHI.Physics.YangMills.BalabanPath13GeneratedLDLResidualsBExact where

open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; -_; _/_)
open import DASHI.Physics.YangMills.BalabanPath13GeneratedLDLResidualsAExact public

------------------------------------------------------------------------
-- Canonical Schur residuals R6..R12.
------------------------------------------------------------------------

residual6 : Path13Coordinates → ℚ
residual6 coordinate =
  (+ 29421908330 / 20877852771) * (y6 coordinate * y6 coordinate) + ((- (+ 39293859025 / 20877852771)) * (y6 coordinate * y7 coordinate) + ((+ 2461846517 / 20877852771) * (y6 coordinate * y8 coordinate) + ((+ 2461846517 / 20877852771) * (y6 coordinate * y9 coordinate) + ((+ 2461846517 / 20877852771) * (y6 coordinate * y10 coordinate) + ((+ 5068507535 / 20877852771) * (y6 coordinate * y11 coordinate) + ((+ 40606059776 / 20877852771) * (y7 coordinate * y7 coordinate) + ((- (+ 41735235655 / 20877852771)) * (y7 coordinate * y8 coordinate) + ((+ 20469887 / 20877852771) * (y7 coordinate * y9 coordinate) + ((+ 20469887 / 20877852771) * (y7 coordinate * y10 coordinate) + ((+ 42143885 / 20877852771) * (y7 coordinate * y11 coordinate) + ((+ 40606059776 / 20877852771) * (y8 coordinate * y8 coordinate) + ((- (+ 41735235655 / 20877852771)) * (y8 coordinate * y9 coordinate) + ((+ 20469887 / 20877852771) * (y8 coordinate * y10 coordinate) + ((+ 42143885 / 20877852771) * (y8 coordinate * y11 coordinate) + ((+ 40606059776 / 20877852771) * (y9 coordinate * y9 coordinate) + ((- (+ 41735235655 / 20877852771)) * (y9 coordinate * y10 coordinate) + ((+ 42143885 / 20877852771) * (y9 coordinate * y11 coordinate) + ((+ 40606059776 / 20877852771) * (y10 coordinate * y10 coordinate) + ((- (+ 41713561657 / 20877852771)) * (y10 coordinate * y11 coordinate) + ((+ 18533246486 / 20877852771) * (y11 coordinate * y11 coordinate)))))))))))))))))))))

residual7 : Path13Coordinates → ℚ
residual7 coordinate =
  (+ 30988088209 / 23537526664) * (y7 coordinate * y7 coordinate) + ((- (+ 11964339425 / 6230521764)) * (y7 coordinate * y8 coordinate) + ((+ 496704103 / 6230521764) * (y7 coordinate * y9 coordinate) + ((+ 496704103 / 6230521764) * (y7 coordinate * y10 coordinate) + ((+ 17384643605 / 105918869988) * (y7 coordinate * y11 coordinate) + ((+ 13447321533 / 6922801960) * (y8 coordinate * y8 coordinate) + ((- (+ 62428358143 / 31152608820)) * (y8 coordinate * y9 coordinate) + ((- (+ 123140503 / 31152608820)) * (y8 coordinate * y10 coordinate) + ((- (+ 50704913 / 6230521764)) * (y8 coordinate * y11 coordinate) + ((+ 13447321533 / 6922801960) * (y9 coordinate * y9 coordinate) + ((- (+ 62428358143 / 31152608820)) * (y9 coordinate * y10 coordinate) + ((- (+ 50704913 / 6230521764)) * (y9 coordinate * y11 coordinate) + ((+ 13447321533 / 6922801960) * (y10 coordinate * y10 coordinate) + ((- (+ 12511748441 / 6230521764)) * (y10 coordinate * y11 coordinate) + ((+ 20648140129 / 23537526664) * (y11 coordinate * y11 coordinate)))))))))))))))

residual8 : Path13Coordinates → ℚ
residual8 coordinate =
  (+ 820548843259 / 660535564455) * (y8 coordinate * y8 coordinate) + ((- (+ 1285278684967 / 660535564455)) * (y8 coordinate * y9 coordinate) + ((+ 35792443943 / 660535564455) * (y8 coordinate * y10 coordinate) + ((+ 14738065153 / 132107112891) * (y8 coordinate * y11 coordinate) + ((+ 24363169043251 / 12550175724645) * (y9 coordinate * y9 coordinate) + ((- (+ 25180252291963 / 12550175724645)) * (y9 coordinate * y10 coordinate) + ((- (+ 32900346983 / 2510035144929)) * (y9 coordinate * y11 coordinate) + ((+ 24363169043251 / 12550175724645) * (y10 coordinate * y10 coordinate) + ((- (+ 5052970636841 / 2510035144929)) * (y10 coordinate * y11 coordinate) + ((+ 2189071617569 / 2510035144929) * (y11 coordinate * y11 coordinate))))))))))

residual9 : Path13Coordinates → ℚ
residual9 coordinate =
  (+ 661887395501231 / 561255408789156) * (y9 coordinate * y9 coordinate) + ((- (+ 551132664563681 / 280627704394578)) * (y9 coordinate * y10 coordinate) + ((+ 20840943993625 / 280627704394578) * (y9 coordinate * y11 coordinate) + ((+ 1089211689931439 / 561255408789156) * (y10 coordinate * y10 coordinate) + ((- (+ 565616556207161 / 280627704394578)) * (y10 coordinate * y11 coordinate) + ((+ 488080695779471 / 561255408789156) * (y11 coordinate * y11 coordinate))))))

residual10 : Path13Coordinates → ℚ
residual10 coordinate =
  (+ 2229938107229224 / 1985662186503693) * (y10 coordinate * y10 coordinate) + ((- (+ 11638177724654623 / 5956986559511079)) * (y10 coordinate * y11 coordinate) + ((+ 1724456159487388 / 1985662186503693) * (y11 coordinate * y11 coordinate)))

residual11 : Path13Coordinates → ℚ
residual11 coordinate =
  (+ 4514842591049713 / 240833315580756192) * (y11 coordinate * y11 coordinate)

residual12 : Path13Coordinates → ℚ
residual12 coordinate = 0ℚ
