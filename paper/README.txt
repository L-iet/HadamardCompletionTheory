Completion theory paper and Lean coverage

The paper retains complete proofs from 26 canonical research sections and
tracks 64 original principal claims individually. Five are now proved:
CT-04-01 (including explicit order12 existence), CT-05-01 (full odd-block
exchange bound and exact ceiling deletion requirement), CT-08-01 (exact quadratic
identity, odd-witness exchange budget and completion consequence), and
CT-08-02 (modulo8 identity, d<=7 lower bound and explicit defect8 zero),
and CT-25-01 (full switch iff and zero-motion restriction). The other59 remain
pending. The Hadamard conjecture is not proved.

There are29 independent comparator targets, synchronized automatically in
Challenge.lean, verified_targets.json and comparator.json. Additional fully
proved classical inputs include genuine codimension-one, two and three
completion, in arbitrary finite indices, with the actual mathlib Hadamard
predicate and retention of all original rows through an injection. The
positive-order unified <=3 theorem assumes divisibility of the order by4.
The special tetrahedral Gram factorization is proved separately. Generic
codimension4 through7 completion remains pending.

Proof modules contain no holes, custom axioms or native_decide. Challenge
contains isolated intentional independent specification placeholders and
imports only mathlib. Solution never imports Challenge. Passing the current
comparator does not certify any pending paper claim. This project remains
not submission-ready. Classical inputs not yet formalized are not axioms
in the Lean proof modules. The arithmetic half-frame result is conditional
on Dirichlet GRH.

Regenerate via python paper/make_challenge.py and python paper/assemble.py.
The assembler reads the self-contained artifacts/research/full_conjecture
archive and writes only this paper directory. Root will batch PDF builds.
