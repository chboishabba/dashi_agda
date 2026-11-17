#!/usr/bin/env python3
"""DASHI Ω V2: source-independent, two-ledger factorial experimental acceptor.

An executable measurement *contract*, not an original V2 dataset. Each measurement
comes from a real signed port or separately inventoried motor/generator state.
Checks are necessary, not sufficient: passing rows cannot establish completeness
of an unknown apparatus' energy boundary or causal controller effects.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path
import argparse, csv, json
from typing import Iterable

ARM_IDS=('00','01','10','11')  # load bit, recovery bit
COLS=(
 'block','sequence','arm','duration_s',
 'motor_input_w','aux_input_w','load_output_w','other_output_w',
 'shaft_transfer_w','motor_loss_w','generator_loss_w',
 'motor_store_before_j','motor_store_after_j',
 'generator_store_before_j','generator_store_after_j',
 'motor_input_err_w','aux_input_err_w','load_output_err_w','other_output_err_w',
 'shaft_transfer_err_w','motor_loss_err_w','generator_loss_err_w',
 'motor_store_endpoint_err_j','generator_store_endpoint_err_j',
)
MEANS=('motor_input_w','aux_input_w','load_output_w','other_output_w',
       'shaft_transfer_w','motor_loss_w','generator_loss_w')
ERROR={k:k.removesuffix('_w')+'_err_w' for k in MEANS}
ERROR.update({'motor_store_rate_w':'motor_store_endpoint_err_j',
              'generator_store_rate_w':'generator_store_endpoint_err_j'})
# All powers are nonnegative oriented in the declared port direction. Reverse
# electrical flow requires an explicitly separate signed component schema.

def rational(x:object)->Q:
    s=str(x).strip()
    if not s or s.lower() in ('nan','inf','-inf','+inf'):
        raise ValueError('missing or nonfinite measurement')
    try:return Q(s)
    except (TypeError,ValueError,ZeroDivisionError) as e:raise ValueError(f'bad rational measurement: {s}') from e

@dataclass(frozen=True)
class Sample:
    block:int
    sequence:int
    arm:str
    values:dict[str,Q]

    @classmethod
    def parse(cls,row:dict)->'Sample':
        if set(row)!=set(COLS):raise ValueError('measurement schema mismatch')
        if any(v is None or not str(v).strip() for v in row.values()):
            raise ValueError('missing field: do not impute zero')
        if not str(row['block']).isdigit() or not str(row['sequence']).isdigit():
            raise ValueError('invalid block or sequence')
        if row['arm'] not in ARM_IDS:raise ValueError('unrecognised factorial arm')
        v={k:rational(row[k]) for k in COLS if k not in ('block','sequence','arm')}
        if v['duration_s']<=0:raise ValueError('non-positive cycle duration')
        if any(z<0 for z in v.values()):raise ValueError('negative oriented port, energy or uncertainty')
        return cls(int(row['block']),int(row['sequence']),row['arm'],v)

    def __getitem__(self,k:str)->Q:
        if k=='motor_store_rate_w':
            return (self.values['motor_store_after_j']-self.values['motor_store_before_j'])/self.values['duration_s']
        if k=='generator_store_rate_w':
            return (self.values['generator_store_after_j']-self.values['generator_store_before_j'])/self.values['duration_s']
        return self.values[k]

    def error(self,k:str)->Q:
        if k.endswith('_store_rate_w'):
            return self.values[ERROR[k]]/self.values['duration_s']
        return self.values[ERROR[k]]

    def residuals(self)->dict[str,Q]:
        v=self
        motor=v['motor_input_w']-v['shaft_transfer_w']-v['motor_loss_w']-v['motor_store_rate_w']
        generator=(v['shaft_transfer_w']+v['aux_input_w']-v['load_output_w']-
                   v['other_output_w']-v['generator_loss_w']-v['generator_store_rate_w'])
        whole=(v['motor_input_w']+v['aux_input_w']-v['load_output_w']-
               v['other_output_w']-v['motor_loss_w']-v['generator_loss_w']-
               v['motor_store_rate_w']-v['generator_store_rate_w'])
        assert motor+generator==whole
        return {'motor':motor,'generator':generator,'whole':whole}

    def residual_error(self,which:str)->Q:
        cols={
          'motor':('motor_input_w','shaft_transfer_w','motor_loss_w','motor_store_rate_w'),
          'generator':('shaft_transfer_w','aux_input_w','load_output_w','other_output_w',
                       'generator_loss_w','generator_store_rate_w'),
          'whole':('motor_input_w','aux_input_w','load_output_w','other_output_w',
                   'motor_loss_w','generator_loss_w','motor_store_rate_w','generator_store_rate_w'),
        }[which]
        return sum((self.error(c) for c in cols),Q())


def design(blocks:int=4)->list[dict]:
    if blocks<=0:raise ValueError('positive block count required')
    result=[]
    for b in range(blocks):
        order=ARM_IDS[b%4:]+ARM_IDS[:b%4]
        for seq,a in enumerate(order+tuple(reversed(order))):
            result.append({'block':b,'sequence':seq,'arm':a})
    return result

def audit(samples:Iterable[Sample],*,stationary=True)->dict:
    blocks:dict[int,dict[str,list[Sample]]]={}
    for r in samples:blocks.setdefault(r.block,{}).setdefault(r.arm,[]).append(r)
    if not blocks:raise ValueError('no data')
    output=[]
    for b,arms in sorted(blocks.items()):
        if set(arms)!=set(ARM_IDS) or any(len(x)!=2 for x in arms.values()):
            raise ValueError('each block requires two of each factorial arm')
        sequences=[r.sequence for pair in arms.values() for r in pair]
        if sorted(sequences)!=list(range(8)):raise ValueError('bad observation positions')
        if any(sum(r.sequence for r in pair)!=7 for pair in arms.values()):
            raise ValueError('linear drift is not balanced')
        for pair in arms.values():
            for r in pair:
                if stationary:
                    for key in ('motor','generator'):
                        e=abs(r.values[f'{key}_store_after_j']-r.values[f'{key}_store_before_j'])
                        if e>r.values[f'{key}_store_endpoint_err_j']:
                            raise ValueError(f'{key} storage not stationary')
                for name,res in r.residuals().items():
                    if abs(res)>r.residual_error(name):
                        raise ValueError(f'{name} signed energy ledger failed')
        keys=MEANS+('motor_store_rate_w','generator_store_rate_w')
        def cm(k):
            return {a:sum((r[k] for r in pairs),Q())/2 for a,pairs in arms.items()}
        def ce(k):
            return {a:sum((r.error(k) for r in pairs),Q())/2 for a,pairs in arms.items()}
        contrast={};bounds={}
        for k in keys:
            a=cm(k);e=ce(k)
            contrast[k]=a['11']-a['10']-a['01']+a['00']
            bounds[k]=sum(e.values(),Q())
        motor=(contrast['motor_input_w']-contrast['shaft_transfer_w']-
               contrast['motor_loss_w']-contrast['motor_store_rate_w'])
        generator=(contrast['shaft_transfer_w']+contrast['aux_input_w']-
                   contrast['load_output_w']-contrast['other_output_w']-
                   contrast['generator_loss_w']-contrast['generator_store_rate_w'])
        whole=motor+generator
        if abs(motor)>sum(bounds[k] for k in ('motor_input_w','shaft_transfer_w','motor_loss_w','motor_store_rate_w')):
            raise ValueError('motor contrast energy failed')
        if abs(generator)>sum(bounds[k] for k in ('shaft_transfer_w','aux_input_w','load_output_w','other_output_w','generator_loss_w','generator_store_rate_w')):
            raise ValueError('generator contrast energy failed')
        output.append({'block':b,
          'interactions_w':{k:float(v) for k,v in contrast.items()},
          'worst_case_interaction_errors_w':{k:float(v) for k,v in bounds.items()},
          'motor_residual_w':float(motor),'generator_residual_w':float(generator),
          'whole_residual_w':float(whole),
          'load_interaction_sign_certified':abs(contrast['load_output_w'])>bounds['load_output_w']})
    return {'schema':'DASHI.V2.Omega.split-motor-generator-storage.v2',
            'status':'measurement acceptance conditional; no original V2 measurements supplied',
            'blocks':output,'original_v2_verified':False,
            'limitations':['an assumed complete instrumented boundary is not proof of a complete physical boundary',
                'common mode calibration biases and non-linear drift are not removed by pairing',
                'a balanced schedule does not control all carryover; randomization and washout need device data',
                'losses must be separately observed, not calculated as an energy-balance residual']}

def template(path:Path,blocks:int=4)->None:
    with path.open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=COLS);w.writeheader()
        for row in design(blocks):w.writerow(row)

def load(path:Path)->list[Sample]:
    with path.open(newline='') as f:return [Sample.parse(r) for r in csv.DictReader(f)]

def main():
    p=argparse.ArgumentParser(description=__doc__)
    g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--template',type=Path);g.add_argument('--measurements',type=Path)
    p.add_argument('--blocks',type=int,default=4)
    p.add_argument('--permit-nonstationary',action='store_true')
    a=p.parse_args()
    if a.template:
        template(a.template,a.blocks)
        print(json.dumps({'template':str(a.template),'rows':8*a.blocks,'contains_original_measurements':False}))
    else:print(json.dumps(audit(load(a.measurements),stationary=not a.permit_nonstationary),indent=2))
if __name__=='__main__':main()
