COMPLETION THEORY

Responsible author and maintainer: Joshua Mark.
ORCID: https://orcid.org/0009-0003-5905-2382

VERIFIED SCOPE: 62/64 principal paper claim records.
Proof development is paused. This release submits only configured proved
declarations. The paper identifies every result outside that scope.
Unsubmitted records: CT-18-01, CT-26-02.
Read paper/main.pdf, paper/ALIGNMENT.json and submission/SCOPE.json.
No full Hadamard-conjecture proof, novelty or registry acceptance is claimed.

BUILD AND SOURCE-BOUND AUDIT
lake exe cache get
python scripts/record_verified_sources.py
python scripts/audit_mathlib_licenses.py
python -m pip install -r scripts/requirements-submission.txt
python scripts/validate_metadata.py
python scripts/build_paper.py
python scripts/refresh_paper_bundle.py

The source recorder performs real ordinary builds of every configured proof
and independent Challenge entry point and audits every compared declaration.
It binds source/config hashes only after those checks succeed unchanged.
Only propext, Classical.choice and Quot.sound are allowed. Intentional proof
placeholders belong only to independent Challenge specifications.
On Windows, HADAMARD_NATIVE_TEX=1 selects the installed native TeX engine.

LOCAL SUBMISSION PREPARATION
python scripts/check_submission.py
python scripts/check_submission_preparation.py

The preparation check covers the explicitly declared verified scope, every
comparison group, current builds/axiom audits, paper/PDF bindings, metadata,
licenses and local dual-kernel evidence. Historical kernel acceptance may be
reused only for byte-identical fresh exports and is labelled in its report.
It is not a fresh registry verification. See submission/PALOMAR_ENTRIES.txt.

SANDBOXED COMPARISON AND REGISTRY PREFLIGHT
python scripts/run_comparator.py
python scripts/check_submission_preparation.py --require-sandbox

Run these on a compatible Linux host with bubblewrap available. Both Lean
and NanoDa acceptance are required for every configured group. The existing
check_submission.py --ready command remains the stronger whole-paper gate;
it intentionally fails if any principal paper claim remains unformalized.

After publishing an immutable commit, the manual "Official Palomar mechanical
preflight" GitHub workflow can check one chosen Comparator configuration
using the pinned official verifier. This workflow is advisory: it performs no
registry submission or registration. One configuration corresponds to one
Palomar entry; multiple configurations must be submitted separately.
No global AppArmor namespace restriction is disabled by this repository's CI.

PUBLICATION STATUS
No commit, push, external workflow dispatch or registry submission was made
as part of this preparation. A public immutable commit and Palomar's actual
mechanical/editorial checks remain external steps. Local preparation reports
must not be described as registry verification or acceptance.

DEPENDENCIES AND LICENSING
Lean 4.35.0, exactly matching pinned mathlib. All nine package revisions
and Apache-2.0/MIT license evidence are recorded in submission/mathlib-licenses.json.
New proof code is original except for the explicitly attributed BSD-3-Clause
translation of the AFP residue-matrix construction. Its author notices,
license and provenance are in CompletionCyclicExistence/. The other original
project code is Apache-2.0. Public papers do not grant code licenses.
Source hashes use canonical LF bytes, avoiding LF/CRLF verification drift.
Local .lake state is a disposable cache and is excluded from Git.

The artifacts directory preserves the earlier author's research proofs,
experiments, data and PDFs for reference. It overlaps companion projects
and does not enlarge this project's formalized claims. Its notice and
snapshot distinguish historical evidence from current verification.

Public repository: https://github.com/L-iet/HadamardCompletionTheory
Use an immutable commit for the declared verified submission scope. Registry
verification and editorial review remain separate submission requirements.

VERIFIED CONFIGURED-TARGET SNAPSHOT
Completed local comparison reports record exported-proof Comparator,
Lean kernel and NanoDa checks for their stated source snapshots. This diagnostic disabled source sandboxing
and is NOT a Palomar run. See submission/local-comparator-result.json.
The standard sandboxed comparison and full principal proof coverage remain
required by --ready. No supporting pass certifies the whole paper.


BOUNDED INDEPENDENT COMPARISON GROUPS
submission/comparison-groups.json lists every required group in this one project:
  comparator.json: Challenge / Solution
  comparator-algorithms.json: AlgorithmChallenge / AlgorithmSolution
Each specification has canonical mathlib/core imports and its own size bound.
The algorithm group has no definition holes. Generated proof obligations are
registered only after checking their kinds and exact types in both environments.

Build/audit every group: python scripts/record_verified_sources.py
Local diagnostics (both required):
  python scripts/run_local_comparator.py
  python scripts/run_local_comparator.py --config comparator-algorithms.json
Sandboxed comparisons on a supported host: python scripts/run_comparator.py
This runs every registered group and requires both independent kernels for each.
A pass for one group does not verify the whole paper. Reports and exports have
separate group paths and must match the same source snapshot. Local diagnostics
are not Palomar registry reports. Registry requests identify the applicable
configuration and immutable commit. These scripts make no commits or submissions.

The small-defect results explicitly retain the classical real-extension input.
The exact candidate-test budget is formalized; the separate scalar-operation
complexity discussion remains outside the compared algorithm theorem.

Finite repair verification: RepairChallenge and comparator-repair.json specify the full one-row augmentation and odd-feasibility results independently. CompletionRepair contains original kernel-only finite certificates, exact integer elimination, and universal bounds. The repair comparison has no definition holes. Run all groups registered in submission/comparison-groups.json.

Order20 code-trap verification: CompletionCodeTrap contains the complete unconditional finite-example proof, including exact sign-class counts, the self-dual pivot neighbor, and the optimal two-row escape for arbitrary real Hadamard matrices. CodeChallenge/comparator-codes.json supplies an independent mathlib-only specification with zero definition holes. Mathematical data are in submission/code-trap-data.json; all proof code is original Apache-2.0 and uses the pinned mathlib dependency. The supplementary full compatibility histogram is a separate computational artifact.

UNCONDITIONAL CYCLIC EXISTENCE INTEGRATION
CompletionCyclicExistence/ contains the three-mod-eight three-square theorem,
fixed-sum four squares and actual uniform/skew cyclic coefficient constructions.
CyclicExistenceChallenge supplies eleven independent theorem targets and nine
concrete definitions. Its public group is comparator-cyclic-existence.json.
The current integration passed full local builds, bounded axiom audits and
all nine local comparison groups on one source snapshot. Full readiness also
requires the remaining principal proofs and registry checks.

The executable build configuration is lakefile.lean. lakefile.toml remains a
machine-readable library catalogue; scripts/check_lake_catalogue.py checks their
agreement. The runtime plugin is restricted to the four libraries that need it.
On the first build, Python3 and the pinned Lean leanc compiler build licensed
mathlib elaborator support under .lake/cyclic-native. This can take substantial
time and disk space. Compilation uses at most two workers and is resumable.
The generated libraries initialize the elaborator; they supply no mathematical
axioms. New proof modules and the axiom-profile reader retain the 1GiB limit.
The existing name-only export preflight keeps its 4GiB diagnostic cap.
All proofs still require standard-axiom audits and independent kernel checks.

Windows runtime/build integration has been exercised locally. Linux handling
is implemented but has not yet been exercised on a clean Linux host. No Linux
registry or Palomar success is inferred. Preserve all license files if copying
sources; .lake generated objects and libraries are disposable and not submitted.

In submission/cyclic-existence-source-provenance.json, the sources array names
and hashes the packaged proof files. The foundationSources array preserves the
original pilot input receipt; its .lake residue-file path is historical. The
public build imports CompletionCyclicExistence/ResidueMatrix.lean and the
existing packaged CompletionTheory/CompletionCharacter foundations.

The bounded axiom audit reads Lean4.35's compiler-generated transitive axiom
cache from each defining olean, the same cache used by imported #print axioms.
It binds source and olean hashes, compares all20cyclic profiles with the stock
command at1GiB, and tests axiom-free, forbidden-builtin and missing-name cases.
The small diagnostic reader uses the pinned type-erased Lean extension format;
it declares no mathematical theorem. Comparator checks actual proof terms with
both independent kernels as a separate required stage.
