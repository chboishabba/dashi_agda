#!/usr/bin/env python3
"""Adversarial local acceptance for source-owned 15/69 exact rows (not orbit)."""
import argparse,json,tempfile
from pathlib import Path
from fractions import Fraction as F
import check_smith_filsinger_j34_69d_exact_rows_20261125 as j

def rejects(test,name):
 try:test()
 except (AssertionError,ValueError,KeyError,TypeError):return
 raise AssertionError('expected negative control to reject: '+name)

def main():
 p=argparse.ArgumentParser();p.add_argument('--j33',type=Path,required=True);p.add_argument('--out',type=Path);args=p.parse_args()
 a=j.source_exact(args.j33)
 assert a['certified_original_69D_F_DF_rows']==15
 assert a['original_69D_missing_F_DF_rows']==54
 assert a['verified_original_pre_switch_guard_slope_signs']==6
 assert a['strict_original_69D_Krawczyk_rows']==0
 assert len(a['missing_source_full_flow_rows'])==6
 assert sum(len(v['rows']) for v in a['missing_source_full_flow_rows'])==54
 results=['15 exact original-source residual/Jacobian rows on nonzero common box',
 '6/6 exact same-clock physical pre-switch transversality signs',
 '6 omitted full-flow blocks kept UNKNOWN, not zero',
 'source-event1 match and wrong V threshold adversarial tests']
 with tempfile.TemporaryDirectory() as dir:
  bad=Path(dir)/'mutated.json';bad.write_bytes(args.j33.read_bytes()+b' ')
  rejects(lambda:j.source_exact(bad),'modified prior J33 complete result SHA256')
 results.append('mutated producer byte content rejected')
 rejects(lambda:j.source_exact(args.j33,state_radius=F(2,10000)),'state box larger than paid J33 source domain')
 results.append('over-wide original 9D input box rejected')
 rejects(lambda:j.source_exact(args.j33,clock_radius=F(1,100000)),'first event outside source-validated time box')
 results.append('over-wide first switching clock rejected')
 rejects(lambda:j.source_exact(args.j33,clock_radius=F(1,10000000)),'time box discards original wide later event brackets')
 results.append('time box failing to contain original J29/J30 brackets rejected')
 original=j.s.MODES
 try:
  modes=list(original);modes[0]=(0,1,1);j.s.MODES=tuple(modes)
  rejects(lambda:j.source_exact(args.j33),'wrong physical starting mode')
 finally:j.s.MODES=original
 results.append('wrong physical-mode source attribution rejected')
 ret=dict(status='PASS_J34_EXACT_SOURCE_69D_ROW_PROVENANCE_AND_NEGATIVE_CONTROLS',passed=len(results),checks=results,
  source_interval_F_DF_paid=15,source_interval_F_DF_missing=54,
  six_original_guard_slopes_strict=6,original_69D_Krawczyk_rows=0,exact_periodic_orbit=False)
 if args.out:args.out.parent.mkdir(parents=True,exist_ok=True);args.out.write_text(json.dumps(ret,indent=2)+'\n')
 print(json.dumps(ret,indent=2))
if __name__=='__main__':main()
