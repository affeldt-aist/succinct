# Compact data structures in Coq

A tentative formalization of compact data structures following [1]

[1] Gonzalo Navarro, Compact Data Structures---A Practical Approach, Cambridge University Press, 2016

# Files

- [compact_data_structures.v](compact_data_structures.v)
- [rank_select.v](rank_select.v)
- [jacobson_rank_complexity.v](jacobson_rank_complexity.v)
- [pred_succ.v](pred_succ.v)
- [louds.v](louds.v)
- [insert_delete.v](insert_delete.v)
- [set_clear.v](set_clear.v)
- [dynamic_redblack.v](dynamic_redblack.v)
- [dynamic_dependent_program.v](dynamic_dependent_program.v)
- [dynamic_dependent_tactic.v](dynamic_dependent_tactic.v)

# Requirements

- Coq 8.9.1
- MathComp 1.9.0

# Compilation

1. `git clone git@github.com:affeldt-aist/succinct.git`
2. `cd succinct`

If the Requirements (see above) are already met, do:

3. `coq_makefile -f _CoqProject -o Makefile`
4. `make`

Or, if opam is installed, do:

3. `opam install .`

opam takes care of the dependencies.

# External Axioms

We do not explicitly introduce any additional axioms. However, [dynamic_dependent_program.v](dynamic_dependent_program.v) and (to a lesser 
extent) [dynamic_dependent_tactic.v](dynamic_dependent_tactic.v) uses the `Program` framework and thus implicitly depends on `Coq.Logic.JMEq.JMEq_eq`, 
which is in turn equivalent to Streicher's Axiom K (i.e., dependent pattern matching).

# Accompanying material

- Most recent [draft paper](201903/compact-20190331.pdf) ([arXiv version](https://arxiv.org/pdf/1904.02809.pdf)), accepted to the 10th International Conference on 
  Interactive Theorem Proving (ITP 2019)
- TPP 2018 slides for [LOUDS](tpp2018/slides_louds_en.pdf) and [dynamic
  bit vectors](tpp2018/slides_dynamic.pdf)
- JSSST 2018 [draft paper](jssst2018/compact.pdf)
- Earlier papers:
  * "[Formal Verification of the *rank* Algorithm for Succinct Data Structures](http://www.math.nagoya-u.ac.jp/~garrigue/papers/succinct-icfem2016.pdf)", in 
    18th International Conference on Formal Engineering Methods (ICFEM 2016)
  * "[Safe Low-level Code Generation in Coq Using Monomorphization and Monadification](http://www.math.nagoya-u.ac.jp/~garrigue/papers/JIP-26_54.pdf)", in 
    *Journal of Information Processing*, vol. 26 (2018)
