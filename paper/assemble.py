"""Curate the project's completion proofs without changing original research files."""
from pathlib import Path
import hashlib
import json
import re

HERE=Path(__file__).resolve().parent
SOURCE=HERE.parent/'artifacts'/'research'/'full_conjecture'
SOURCES=[
 ('cyclic-hermitian-norms','arithmetic/large_energy.tex'),
 ('quadratic-character-floor','round3/arithmetic/sharp_character_span.tex'),
 ('residual-foundations','paper/research.tex'),
 ('residual-lattices','round5/completion.tex'),
 ('exchange-budget','round6/completion/completion.tex'),
 ('partial-frame-exchanges','exchanges/results.tex'),
 ('tensor-exchange-barrier','round3/exchanges/tensor_barrier.tex'),
 ('parity-lattices','round7/repair/repair.tex'),
 ('short-coset-repair','round8/lattice/lattice.tex'),
 ('modular-lifting-eight','round9/lattice/lattice.tex'),
 ('modular-lifting-four','round10/modular/modular.tex'),
 ('compatible-codes','round10/codes/codes.tex'),
 ('terminal-code-trap','round10/code_traps/traps.tex'),
 ('neighbor-incidence','round10/codes/neighbor_counts.tex'),
 ('quotient-grid','round11/quotients/quotients.tex'),
 ('completion-moments','round11/moments/moments.tex'),
 ('third-moments','round12/moments/third.tex'),
 ('conditional-half-frame','round12/arithmetic/arithmetic.tex'),
 ('real-dilations','round12/dilations/dilations.tex'),
 ('quaternary-realification','round13/quaternary/quaternary.tex'),
 ('weighing-normal-form','round13/weighing/weighing.tex'),
 ('real-weighing-exactness','round14/weighing/weighing.tex'),
 ('complex-defect-two','round14/phase_quantum/completion.tex'),
 ('quaternary-defect-three','round15/completion/main.tex'),
 ('support-moving-repair','round15/weighing/main.tex'),
 ('complete-neighbor-census','round11/landscape/landscape.tex'),
]


def run():
    sections=HERE/'sections';sections.mkdir(parents=True,exist_ok=True)
    inventory=[];targets=[];inputs=[];needed_citations=set()
    for number,(slug,relative) in enumerate(SOURCES,1):
        path=SOURCE/relative
        content=path.read_text(encoding='utf-8-sig')
        if slug=='residual-foundations':
            content=content.split(r'\section{Lattices, tight frames and completion}',1)[1]
            content=r'\section{Residual Gram foundations and fixed-defect decisions}'+content.split(r'\subsection{A valid-order obstruction and a successful repair}',1)[0]
        if r'\begin{document}' in content:
            content=content.split(r'\begin{document}',1)[1].split(r'\end{document}',1)[0]
            content=content.replace(r'\maketitle','')
            content=re.sub(r'\\begin\{abstract\}.*?\\end\{abstract\}', '', content, flags=re.S)
            if slug=='complete-neighbor-census':
                content=r'\section{Syndrome census and the complete improving-neighbor landscape}'+ '\n'+content
            if slug=='cyclic-hermitian-norms':
                content=r'\section{Large-energy cyclic Hermitian norms}'+ '\n'+content
        content=content.split(r'\begin{thebibliography}',1)[0]
        dest=f'{number:02}-{slug}.tex'
        (sections/dest).write_text(content.rstrip()+'\n',encoding='utf-8')
        inputs.append(r'\input{sections/'+dest+'}')
        claims=[]
        pattern=r'\\begin\{(theorem|proposition|corollary|lemma)\}(?:\[([^\]]*)\])?'
        for item,match in enumerate(re.finditer(pattern,content),1):
            target=f'CT-{number:02}-{item:02}'
            statement=content[match.end():].split(r'\begin{proof}',1)[0]
            statement=re.split(r'\\end\{(?:theorem|proposition|corollary|lemma)\}',statement,maxsplit=1)[0].strip()
            record={'id':target,'section':dest,'kind':match.group(1),
                    'title':match.group(2) or f'{slug} {match.group(1)} {item}',
                    'statement_tex':statement,'lean_status':'pending',
                    'lean_declaration':None,'reason':'The full paper statement is not yet formalized.'}
            if target=='CT-03-01':
                record.update(lean_status='proved',
                    lean_declaration='CompletionTheory.residual_factor_completion_iff',
                    lean_declarations=['CompletionTheory.residual_factor_completion_iff','CompletionTheory.residualGram_structure','CompletionTheory.residualGram_diagonal','CompletionTheory.residualGram_offDiagonal_parity'],
                    reason='Actual residual positive semidefiniteness, exact missing-row rank, scaled projection identity, diagonal and off-diagonal parity, and sign-factor iff standard mathlib Hadamard completion retaining all original rows. Sum-index coordinates represent missing and retained rows without extra algebraic hypotheses.')
            if target=='CT-03-03':
                record.update(lean_status='proved',
                    lean_declaration='CompletionTheory.even_order_defect_two_completion',
                    lean_declarations=['CompletionTheory.even_order_defect_two_completion'],
                    reason='Every even order n>=2 is covered with n-2 original rows retained through an explicit injection, using the proved codimension-two completion theorem.')
            if target=='CT-04-01':
                record.update(lean_status='proved',
                    lean_declaration='CompletionTheory.odd_repetition_unextendible',
                    lean_declarations=['CompletionTheory.repetition_partialHadamard','CompletionTheory.odd_repetition_unextendible','CompletionTheory.eight_missing_rows_obstruction','CompletionTheory.seedTwelve_hadamard'],
                    reason='Exact repeated-frame construction and general odd-block no-extension theorem, plus explicit four-by-twelve obstruction and a kernel-checked order-twelve Hadamard matrix.')
            if target=='CT-05-01':
                record.update(lean_status='proved',
                    lean_declaration='CompletionTheory.odd_block_exchange_budget',
                    lean_declarations=['CompletionTheory.odd_block_exchange_budget'],
                    reason='Exact L<=k*s^2 arbitrary insertion bound and natural ceiling deletion requirement, obtained using the proved zero-budget block-indicator witness.')
            if target=='CT-08-01':
                record.update(lean_status='proved',
                    lean_declaration='CompletionTheory.weighted_odd_witness_budget',
                    lean_declarations=['CompletionTheory.witnessBudget_eq_residual','CompletionTheory.weighted_odd_witness_budget'],
                    reason='Exact residual quadratic identity, nonnegative budget, weighted arbitrary row-exchange inequality and its full-completion consequence. Retained set S is complement of deleted set D.')
            if target=='CT-08-02':
                record.update(lean_status='proved',
                    lean_declaration='CompletionTheory.witnessBudget_mod_eight',
                    lean_declarations=['CompletionTheory.witnessBudget_mod_eight','CompletionTheory.small_defect_budget','CompletionTheory.defect_eight_zero'],
                    reason='Exact integer congruence C_f=(N-r)+8*t, the full d<=7 nonnegative-budget consequence, and an explicit odd-sum zero-budget 4-by-12 witness at defect8.')
            if target=='CT-25-01':
                record.update(lean_status='proved',
                    lean_declaration='CompletionTheory.walshLift_switch_iff',
                    lean_declarations=['CompletionTheory.walshLift_switch_iff','CompletionTheory.walshLift_support_motion'],
                    reason='Exact necessary-and-sufficient switch and support-motion conclusion, for arbitrary weight and selected two-zero/full-sign column shapes; specializes to normalized W(n,n-2).')
            claims.append(target);targets.append(record)
        inventory.append({'id':f'CT-S{number:02}','source':str(path.relative_to(SOURCE)).replace('\\','/'),
                          'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
                          'local_section':f'sections/{dest}','claim_ids':claims,
                          'scope':'Original proof retained; classical inputs and conditional hypotheses remain explicit.'})
        for keys in re.findall(r'\\cite(?:\[[^\]]*\])?\{([^}]+)\}',content):
            needed_citations.update(keys.split(','))
    # Reuse the author's existing bibliographic records, never guessed references.
    bibliography={}
    for path in SOURCE.rglob('*.tex'):
        content=path.read_text(encoding='utf-8-sig')
        for match in re.finditer(r'\\bibitem(?:\[[^\]]*\])?\{([^}]+)\}',content):
            rest=content[match.end():]
            text=re.split(r'\\bibitem|\\end\{thebibliography\}',rest,maxsplit=1)[0].strip()
            bibliography.setdefault(match.group(1),text)
    missing=needed_citations-bibliography.keys()
    if missing:raise RuntimeError(f'Unresolved primary references: {sorted(missing)}')
    bib='\n'.join(r'\bibitem{'+key+'} '+bibliography[key] for key in sorted(needed_citations))
    preamble=r'''\documentclass[11pt]{article}
\usepackage[margin=1in]{geometry}
\usepackage[T1]{fontenc}
\usepackage{lmodern,amsmath,amssymb,amsthm,hyperref,array}
\setlength{\emergencystretch}{3em}
\setcounter{MaxMatrixCols}{20}
\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{proposition}[theorem]{Proposition}
\newtheorem{corollary}[theorem]{Corollary}
\newtheorem{definition}[theorem]{Definition}
\newtheorem{question}[theorem]{Question}
\newcommand{\R}{\mathbb R}
\newcommand{\C}{\mathbb C}
\newcommand{\F}{\mathbb F}
\newcommand{\Z}{\mathbb Z}
\newcommand{\tr}{\operatorname{tr}}
\newcommand{\rank}{\operatorname{rank}}
\newcommand{\Sym}{\operatorname{Sym}}
\newcommand{\Skew}{\operatorname{Skew}}
\title{Arithmetic, completion and repair of Hadamard frames}
\author{Joshua Mark\thanks{ORCID: \href{https://orcid.org/0009-0003-5905-2382}{0009-0003-5905-2382}. AI tools assisted with research, derivation, checking and formalization.}}
\date{21 November 2026 --- consolidated research paper; formalization in progress}
\begin{document}
\maketitle
\begin{abstract}
We organize arithmetic, completion and repair results for real and fourth-root Hadamard
frames. The results distinguish sign feasibility from integer or rational
Gram completion, give exact residue and code-neighbor counts, reduce
codimension-two compatible completion to a weighted grid, and describe
two-zero weighing completion through a finite matrix kernel. A real
zero-supported completion in that weighing setting exists exactly when
a sign completion does; a support-moving switch repairs an explicit
obstruction. Further sections give real and quaternary residual tests,
small-codimension completion with its classical input explicit, and a
conditional GRH transfer from sparse multibase existence to half-frames.
The accompanying Lean development verifies supporting algebra, finite Walsh
identities, and several complete research statements. Proved and pending
claims are individually tracked in ALIGNMENT.json. No claim of complete
formal verification or an all-order Hadamard existence proof is made.
\end{abstract}
\tableofcontents
\section*{Organization and exact scope}
The first group studies cyclic Hermitian norm constructions, residual lattices and modular sign counts. The
second develops compatible self-dual codes, retained-space quotients and
completion moments. The third treats real/quaternary dilations and near-full
weighing matrices, ending with an explicit support-moving repair.
Classical completion and conference theorems are named at their use sites;
they are mathematical inputs, not new assumptions added to Lean. The GRH
result is explicitly conditional. Exact finite certificates support the
specified examples and are not substitutes for general proofs.

This paper retains the full proofs from the corresponding research sections,
with source hashes in INVENTORY.json. Repeated definitions in these groups
have their stated local dimensions and fields. The companion PhaseGeometry
paper owns analytic landscape and discrete Gram-energy move results;
RootEntropyDesigns owns general moment-polytope and collision-entropy
results. Only their completion interfaces are used here.

\section*{What the current Lean development proves}
The public namespace is \texttt{CompletionTheory}. It defines actual sign
matrices, partial Hadamard Gram identities and weighing matrices, and proves
horizontal Gram concatenation, orthogonal row-map invariance and a complete
orthogonal-design filling implication with the standard mathlib Hadamard
predicate as conclusion. It also proves the normalized four-row Walsh
identity, the exact full-support sign criterion, and the complete ambient
four-row weighing operation for admissible columns. These are supporting results, not
weakened replacements for any pending principal theorem below. The full
four-row switch equivalence and zero-motion conclusion are formalized as
\texttt{walshLift\_switch\_iff} and \texttt{walshLift\_support\_motion}
(target CT-25-01). Comparator
targets are limited to declarations whose proofs compile. Every remaining
claim has a stable identifier and pending status in ALIGNMENT.json.
The even-order defect-two completion statement is formalized as
\texttt{even\_order\_defect\_two\_completion} (CT-03-03), retaining every
original row through an explicit injection.
The exact residual criterion (CT-03-01) is also formalized, including
positive semidefiniteness, rank, the scaled projection identity, diagonal
and parity statements, and the equivalence with a sign Gram factor.
'''
    main=preamble+'\n'.join(inputs)+'\n'+r'\input{formalized-completion}'+'\n'
    if bib:main+=r'\begin{thebibliography}{99}'+'\n'+bib+'\n'+r'\end{thebibliography}'+'\n'
    main+=r'\end{document}'+'\n'
    (HERE/'main.tex').write_text(main,encoding='utf-8')
    overlap=[{'source':'paper/research.tex: lattice/tight-frame foundations','destination':'CompletionTheory foundations; superseded by later retained full proofs'},
             {'source':'round5/collision_entropy.tex: rank<=3 real completion interface','destination':'RootEntropyDesigns owns full entropy proof; cited classical/input interface here'},
             {'source':'exchanges/results.tex, round3/exchanges/tensor_barrier.tex','destination':'CompletionTheory retains the full partial-Hadamard augmentation proofs'},
             {'source':'round9/exchanges/, round10/exchanges/, round15/exchanges/','destination':'RootEntropyDesigns owns fair-bit atom exchange; PhaseGeometry owns discrete Gram-energy strip moves'},
             {'source':'round8/nonlinear/, round9/nonlinear/, round10/nonlinear/, round13/quantum/, round14/phase_quantum/paper.tex','destination':'PhaseGeometry owns ambient analytic/quantum obstructions; real and quaternary completion interfaces retained here'}]
    (HERE/'INVENTORY.json').write_text(json.dumps({'project':'CompletionTheory','sections':inventory,'overlap_and_cross_references':overlap},indent=2)+'\n',encoding='utf-8')
    (HERE/'ALIGNMENT.json').write_text(json.dumps({'project':'CompletionTheory','all_milestones_complete':False,'ready':False,
        'principal_claims':targets,'formalized_supporting_results':[
          {'id':f'CT-SUPPORT-{i:03d}','lean':name,'status':'compiled','verification':'lake build CompletionTheory Challenge Solution; Lean 4.35.0'}
          for i,name in enumerate(json.loads((HERE.parent/'verified_targets.json').read_text(encoding='utf-8'))['theorem_names'],1)],
        'formalized_additional_results':[{'id':'CT-EXTRA-TETRAHEDRAL','lean_declarations':['CompletionTheory.tetrahedral_sign_factor','CompletionTheory.tetrahedral_completion_of_card'],'status':'proved','statement':'Any codimension-three real sign frame with switched off-diagonal column correlations -3 or 1 completes, retaining all rows. This does not assert arbitrary codimension-three completion.'}],
        'formalized_classical_inputs':[{'id':'CT-CLASSICAL-CODIM-THREE','lean':'CompletionTheory.codimension_le_three_completion','lean_declarations':['CompletionTheory.codimension_one_completion_of_card','CompletionTheory.codimension_two_completion_of_card','CompletionTheory.codimension_three_completion_of_card','CompletionTheory.codimension_le_three_completion'],'status':'proved','statement':'Every positive-order partial sign Hadamard of order divisible by four with at most three missing rows completes, retaining all original rows through an injection. No completion theorem is assumed.'},{'id':'CT-CLASSICAL-CODIM-TWO','lean':'CompletionTheory.codimension_two_completion','status':'proved','statement':'Every even-order sign frame of codimension two completes, retaining every original row.'},{'id':'CT-CLASSICAL-CODIM-ONE','lean':'CompletionTheory.codimension_one_completion','status':'proved','statement':'Every n by n+1 partial real Hadamard frame completes, retaining every original row.'}],
        'classical_inputs':['Real codimension-at-most-seven completion theorem','Conference normalization theorem','Paley constructions','Finite-field hyperbolic geometry','Lagrange four-square theorem','Dirichlet GRH only in the explicitly conditional arithmetic section'],
        'policy':'No pending principal statement is represented by a weaker formal target or assumed as a Lean axiom.'},indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'sections':len(inventory),'principal_claims':len(targets),'pending_principal_claims':sum(x['lean_status']=='pending' for x in targets),'citations':sorted(needed_citations)}))

if __name__=='__main__':run()
