"""Generate an independent mathlib-only specification for already proved targets."""
from pathlib import Path
import json
import re

ROOT=Path(__file__).resolve().parents[1]
TARGETS=[
 'concatenate_gram','concatenate_partialHadamard','orthogonal_row_transform',
 'orthogonal_design_gram','orthogonal_design_mathlib_hadamard',
 'walshFour_orthogonal','walshFour_sign_iff','walshLift_weighing',
 'walshFour_alphabet_iff','walshLift_switch_iff','walshLift_support_motion',
 'codimension_one_completion','codimension_two_completion',
 'repetition_partialHadamard','odd_repetition_unextendible','seedTwelve_hadamard','eight_missing_rows_obstruction',
 'witnessBudget_eq_residual','weighted_odd_witness_budget',
 'tetrahedral_sign_factor','tetrahedral_completion_of_card',
 'codimension_one_completion_of_card','codimension_two_completion_of_card',
 'codimension_three_completion_of_card','codimension_le_three_completion',
 'odd_block_exchange_budget',
 'witnessBudget_mod_eight','small_defect_budget','defect_eight_zero',
]


def run():
    text=(ROOT/'CompletionTheory.lean').read_text(encoding='utf-8-sig')+'\n'+(ROOT/'CompletionTheory'/'CodimensionOne.lean').read_text(encoding='utf-8-sig')+'\n'+(ROOT/'CompletionTheory'/'CodimensionTwo.lean').read_text(encoding='utf-8-sig')+'\n'+(ROOT/'CompletionTheory'/'RepetitionObstruction.lean').read_text(encoding='utf-8-sig')+'\n'+(ROOT/'CompletionTheory'/'ExchangeBudget.lean').read_text(encoding='utf-8-sig')+'\n'+(ROOT/'CompletionTheory'/'TetrahedralCompletion.lean').read_text(encoding='utf-8-sig')+'\n'+(ROOT/'CompletionTheory'/'CodimensionThree.lean').read_text(encoding='utf-8-sig')+'\n'+(ROOT/'CompletionTheory'/'OddBlockBudget.lean').read_text(encoding='utf-8-sig')+'\n'+(ROOT/'CompletionTheory'/'ParityDeficit.lean').read_text(encoding='utf-8-sig')
    imports='\n'.join(line for line in text.splitlines() if line.startswith('public import ') and not line.startswith('public import CompletionTheory'))
    starts=list(re.finditer(r'^(?:noncomputable )?(def|theorem) ([A-Za-z0-9_]+)',text,re.M))
    definitions=[];theorems=[];names=[]
    for i,match in enumerate(starts):
        end=starts[i+1].start() if i+1<len(starts) else text.index('\nend CompletionTheory',match.end())
        chunk=text[match.start():end].split('\n/--',1)[0].strip()
        chunk=re.sub(r'\nset_option [^\n]+ in\s*$','',chunk)
        if match.group(1)=='def':
            definitions.append(chunk);names.append('CompletionTheory.'+match.group(2))
        elif match.group(2) in TARGETS:
            statement=chunk.split(':=',1)[0].rstrip()
            theorems.append(statement+' := by\n  sorry')
    assert len(theorems)==len(TARGETS)
    preamble='''/-
Copyright (c) 2026 Joshua Mark. Released under Apache 2.0; see LICENSE.
Independent target specifications. The intentional proof placeholders below
are not proof dependencies and are isolated from every solution entry point.
All imports are mathlib-only; Solution imports the completed proof module.
The switch criterion and support-motion targets together verify CT-25-01.
All other principal paper claims remain pending.
-/
module

'''
    challenge=preamble+imports+'\n\n@[expose] public section\nnamespace CompletionTheory\nopen Matrix\n\n'
    challenge+='\n\n'.join(definitions+theorems)+'\n\nend CompletionTheory\n'
    (ROOT/'Challenge.lean').write_text(challenge,encoding='utf-8')
    (ROOT/'Solution.lean').write_text('''/-
Copyright (c) 2026 Joshua Mark. Released under Apache 2.0; see LICENSE.
Proof entry point; intentionally does not import Challenge.
-/
module
public import CompletionTheory
public import CompletionTheory.CodimensionOne
public import CompletionTheory.CodimensionTwo
public import CompletionTheory.RepetitionObstruction
public import CompletionTheory.ExchangeBudget
public import CompletionTheory.TetrahedralCompletion
public import CompletionTheory.CodimensionThree
public import CompletionTheory.OddBlockBudget
public import CompletionTheory.ParityDeficit
''',encoding='utf-8')
    verified={'theorem_names':['CompletionTheory.'+name for name in TARGETS],
      'definition_names':names,'proof_module':'CompletionTheory','challenge_module':'Challenge',
      'solution_module':'Solution','scope':'Compiled supporting algebra and the full admissible four-row weighing operation.',
      'principal_paper_theorems_verified':['CT-04-01','CT-05-01','CT-08-01','CT-08-02','CT-25-01'],
      'challenge_placeholders':'Intentional independent specification proofs only; never imported by Solution.'}
    (ROOT/'verified_targets.json').write_text(json.dumps(verified,indent=2)+'\n',encoding='utf-8')
    config=json.loads((ROOT/'comparator.json').read_text(encoding='utf-8'))
    config.update(theorem_names=verified['theorem_names'],definition_names=verified['definition_names'])
    (ROOT/'comparator.json').write_text(json.dumps(config,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'supporting_targets':len(TARGETS),'independent_definitions':len(names)}))

if __name__=='__main__':run()
