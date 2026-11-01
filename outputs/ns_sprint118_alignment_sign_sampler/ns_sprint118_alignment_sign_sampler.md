# ns_sprint118_alignment_sign_sampler

Deterministic HH-to-low strain alignment sign sampler.

Formula surface:

- contraction = lambda * cos2 for one eigenvector contribution
- Pi_HH_to_L sign = sign(-contraction)
- compressive aligned rows use lambda < 0 and cos2 > 0
- extensive rows use lambda > 0 and are not positive flux rows

Pointwise sign under alignment recorded: true.
Kinematic condition recorded: true.
Persistent alignment existence closed: false.
Non-circular geometric correlation source closed: false.
Clay promoted: false.

| lambda | cos^2 | contraction | Pi_HH_to_L sign | compressive | extensive | positive flux |
| --- | --- | --- | --- | --- | --- | --- |
| -2 | 0 | -0 | 0 | true | false | false |
| -2 | 0.25 | -0.5 | 1 | true | false | true |
| -2 | 0.5 | -1 | 1 | true | false | true |
| -2 | 0.75 | -1.5 | 1 | true | false | true |
| -2 | 1 | -2 | 1 | true | false | true |
| -1 | 0 | -0 | 0 | true | false | false |
| -1 | 0.25 | -0.25 | 1 | true | false | true |
| -1 | 0.5 | -0.5 | 1 | true | false | true |
| -1 | 0.75 | -0.75 | 1 | true | false | true |
| -1 | 1 | -1 | 1 | true | false | true |
| 0 | 0 | 0 | 0 | false | false | false |
| 0 | 0.25 | 0 | 0 | false | false | false |
| 0 | 0.5 | 0 | 0 | false | false | false |
| 0 | 0.75 | 0 | 0 | false | false | false |
| 0 | 1 | 0 | 0 | false | false | false |
| 1 | 0 | 0 | 0 | false | true | false |
| 1 | 0.25 | 0.25 | -1 | false | true | false |
| 1 | 0.5 | 0.5 | -1 | false | true | false |
| 1 | 0.75 | 0.75 | -1 | false | true | false |
| 1 | 1 | 1 | -1 | false | true | false |
| 2 | 0 | 0 | 0 | false | true | false |
| 2 | 0.25 | 0.5 | -1 | false | true | false |
| 2 | 0.5 | 1 | -1 | false | true | false |
| 2 | 0.75 | 1.5 | -1 | false | true | false |
| 2 | 1 | 2 | -1 | false | true | false |
