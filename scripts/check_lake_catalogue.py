# SPDX-License-Identifier: Apache-2.0
"""Ensure build metadata and executable Lake targets agree."""
from pathlib import Path
import re,tomllib
ROOT=Path(__file__).resolve().parents[1]
def check_lake_catalogue():
    catalogue=tomllib.loads((ROOT/'submission/lake-catalogue.toml').read_text(encoding='utf-8'))
    lean=(ROOT/'lakefile.lean').read_text(encoding='utf-8')
    blocks=re.findall(r'(?m)^(?:(@\[default_target\])\n)?lean_lib (\w+) where\n(.*?)(?=^lean_lib |^@\[default_target\]|\Z)',lean,re.S|re.M)
    assert [name for _,name,_ in blocks]==[row['name'] for row in catalogue['lean_lib']], 'Lake library catalogue mismatch'
    assert [name for default,name,_ in blocks if default]==catalogue['defaultTargets'], 'Default Lake targets mismatch'
    for (_,name,body),row in zip(blocks,catalogue['lean_lib']):
        args=re.search(r'moreLeanArgs := #\[(.*?)\]',body)
        actual=re.findall(r'"([^"]*)"',args[1]) if args else []
        assert actual==row.get('moreLeanArgs',[]), 'Proof compiler arguments mismatch: '+name
        assert ('plugins := #[{key := .packageTarget .anonymous `nativeRuntime}]' in body)==(name in {'Solution','CompletionCyclicExistence','CyclicExistenceChallenge','CyclicExistenceSolution'}), 'Native plugin scope mismatch: '+name
    pin=catalogue['require'][0]
    assert ('require mathlib from git "'+pin['git']+'" @ "'+pin['rev']+'"') in lean
    assert 'extraDepTargets := #[`nativeRuntime]' in lean
if __name__=='__main__':
    check_lake_catalogue()
    print('Executable Lake targets, proof limits, defaults and dependency pin agree with catalogue.')
