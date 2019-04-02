# Compact data structures in Coq

A tentative formalization of compact data structures following [1]

[1] Gonzalo Navarro, Compact Data Structures---A Practical Approach, Cambridge University Press, 2016

# Files

- [compact_data_structures.v](compact_data_structures.v)
- [rank_select.v](rank_select.v)
- [jacobson_rank_complexity.v](jacobson_rank_complexity.v)
- [louds.v](louds.v)
- [insert_delete.v](insert_delete.v)
- [set_clear.v](set_clear.v)
- [dynamic_redblack.v](dynamic_redblack.v)
- [dynamic_dependent_program.v](dynamic_dependent_program.v)
- [dynamic_dependent_tactic.v](dynamic_dependent_tactic.v)

# Compilation

1. `coq_makefile -f _CoqProject -o Makefile`
2. `make`

# Accompanying material

- Most recent [draft paper](201903/compact-20190331.pdf)
- TPP 2018 slides for [LOUDS](tpp2018/slides_louds_en.pdf) and [dynamic
  bit vectors](tp2018/slides_dynamic.pdf)
- JSSST 2018 [draft paper](jssst2018/compact.pdf)
