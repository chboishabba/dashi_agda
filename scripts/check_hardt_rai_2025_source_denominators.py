#!/usr/bin/env python3
"""Paper/repository/code-source denominator audit; NOT original EEG reproduction.

Paper: Rai et al. iScience (2025) DOI 10.1016/j.isci.2025.112922.
Dataset: Rai and Orgs UCL RDR v1 DOI 10.5522/04/28508744.v1.
The authors own both records and data. A discrepancy is an unresolved
version/coverage JOIN, not proof of a study error or invented participants.
"""
from __future__ import annotations
from itertools import combinations
import argparse
import json
from pathlib import Path

PAPER = dict(recruited=69, lost_technical=9, lost_markers=1,
             retained=59, performances=(20, 18, 21))
DEPOSIT = dict(declared_recordings=57, accession='28508744',
               doi='10.5522/04/28508744.v1', license='CC0 1.0')
CODE_LOCATORS = ('https://osf.io/uz573/', 'https://osf.io/ursmc/')


def audit_metadata(paper=PAPER, deposit=DEPOSIT):
    if paper['recruited']-paper['lost_technical']-paper['lost_markers'] != paper['retained']:
        raise ValueError('publication recruitment/exclusion arithmetic')
    if sum(paper['performances']) != paper['retained']:
        raise ValueError('publication retained event counts')
    if deposit['declared_recordings'] > paper['retained'] or deposit['declared_recordings'] < 0:
        raise ValueError('deposit numerical coverage outside publication cohort')
    n=paper['performances']
    pair_counts=tuple(k*(k-1)//2 for k in n)
    return dict(paper_recruited=paper['recruited'],
                paper_reported_excluded=paper['lost_technical']+paper['lost_markers'],
                paper_retained=paper['retained'],
                published_event_counts=list(n),
                synthetic_max_same_event_pair_combinations=list(pair_counts),
                synthetic_max_all_event_pairs=sum(pair_counts),
                dataset_catalog_declared_recordings=deposit['declared_recordings'],
                nominal_record_gap=paper['retained']-deposit['declared_recordings'],
                deposit_doi=deposit['doi'], deposit_license=deposit['license'],
                osf_code_locators=list(CODE_LOCATORS),
                osf_code_identical_or_different_verified=False,
                original_file_inventory_verified=False,
                participant_membership_join_verified=False,
                real_eeg_reanalysis_verified=False,
                transmitter_to_receiver_effect_verified=False)


def subject_join(paper_ids, archive_ids):
    """Join supplied anonymised IDs only; their origin cannot be certified here."""
    p=list(paper_ids); a=list(archive_ids)
    if len(p)!=len(set(p)) or len(a)!=len(set(a)):
        raise ValueError('duplicate participant or recording ID')
    if not all(isinstance(x,str) and x.strip() for x in p+a):
        raise ValueError('missing anonymised identity')
    return dict(paper_ids=len(p),archive_ids=len(a),
                matched_ids=len(set(p)&set(a)),
                published_not_in_archive=sorted(set(p)-set(a)),
                archive_not_in_published=sorted(set(a)-set(p)),
                ids_authenticated_by_original_data=False,
                paper_archive_subset_verified=set(a).issubset(set(p)),
                cross_source_join_is_a_measurement_receipt=False)


def audit_manifest_file(path:Path):
    obj=json.loads(path.read_text(encoding='utf-8'))
    required=('paper_doi','deposit_doi','paper_retained','deposit_declared','paper_ids','archive_ids')
    if not isinstance(obj,dict) or any(x not in obj for x in required):
        raise ValueError('manifest missing original accession/identity fields')
    if obj['paper_doi']!='10.1016/j.isci.2025.112922' or obj['deposit_doi']!=DEPOSIT['doi']:
        raise ValueError('not same source publication/deposit identifiers')
    if obj['paper_retained']!=59 or obj['deposit_declared']!=57:
        raise ValueError('paper/deposit counts not source-locked')
    joined=subject_join(obj['paper_ids'],obj['archive_ids'])
    if joined['paper_ids']!=59 or joined['archive_ids']!=57:
        raise ValueError('not a complete source-specific identifier reconciliation')
    return joined


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--manifest',type=Path)
    a=p.parse_args()
    output=audit_manifest_file(a.manifest) if a.manifest else audit_metadata()
    print(json.dumps(output,sort_keys=True,indent=2))


if __name__=='__main__':main()
