# SPDX-License-Identifier: Apache-2.0
"""Validated native elaborator initialization; supplies no mathematical axioms."""
from pathlib import Path
import hashlib,json,subprocess,sys
ROOT=Path(__file__).resolve().parents[1]
def native_lean_args():
    subprocess.run([sys.executable,str(ROOT/'scripts/bootstrap_native_mathlib.py'),'--project-root',str(ROOT)],cwd=ROOT,check=True)
    data=json.loads((ROOT/'.lake/cyclic-native/result.json').read_text(encoding='utf-8'))
    loader=Path(data['loader']['file'])
    assert hashlib.sha256(loader.read_bytes()).hexdigest()==data['loader']['sha256']
    return ['--plugin='+str(loader)]
