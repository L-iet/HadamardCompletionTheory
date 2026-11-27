# SPDX-License-Identifier: Apache-2.0
"""Reject executable build drift without changing real project files."""
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch
import unittest,shutil
import check_lake_catalogue as catalogue
ROOT=Path(__file__).resolve().parents[1]
class LakeCatalogueTest(unittest.TestCase):
    def setUp(self):
        (ROOT/'.lake').mkdir(exist_ok=True)
        self.temp=TemporaryDirectory(dir=ROOT/'.lake')
        self.root=Path(self.temp.name)
        assert self.root.resolve().is_relative_to((ROOT/'.lake').resolve())
        (self.root/'submission').mkdir()
        for name in ['submission/lake-catalogue.toml','lakefile.lean']:shutil.copy2(ROOT/name,self.root/name)
    def tearDown(self):self.temp.cleanup()
    def check(self):
        with patch.object(catalogue,'ROOT',self.root):catalogue.check_lake_catalogue()
    def change(self,old,new):
        p=self.root/'lakefile.lean';s=p.read_text(encoding='utf-8');self.assertIn(old,s)
        p.write_text(s.replace(old,new,1),encoding='utf-8',newline='\n')
    def test_current_configuration(self):self.check()
    def test_unrecorded_proof_limit_rejected(self):
        self.change('lean_lib CompletionCyclicExistence where\n  moreLeanArgs := #["-M4096"]','lean_lib CompletionCyclicExistence where\n  moreLeanArgs := #["-M2048"]')
        with self.assertRaisesRegex(AssertionError,'compiler arguments'):self.check()
    def test_default_target_drift_rejected(self):
        self.change('@[default_target]\nlean_lib CompletionTheory where','lean_lib CompletionTheory where')
        with self.assertRaisesRegex(AssertionError,'Default Lake targets'):self.check()
    def test_runtime_plugin_omission_rejected(self):
        self.change('lean_lib Solution where\n  plugins := #[{key := .packageTarget .anonymous `nativeRuntime}]','lean_lib Solution where')
        with self.assertRaisesRegex(AssertionError,'Native plugin scope'):self.check()
if __name__=='__main__':unittest.main()
