# Exact CAS Core

`prec_cas.hpp` provides the first symbolic layer for prec-cpp. It deliberately
keeps exact values separate from symbolic expressions:

- `exact_value` is an integer, reduced rational, or approximate `Number`.
- `exact_expr` is a small handle to an immutable expression DAG.
- `exact_context` owns the shared node arena and constructs canonical nodes.
- `exact_add_builder` folds numeric terms before they enter the arena.

## Example

```cpp
#include"prec_cas.hpp"

exact_context cas;
exact_expr x = cas.symbol("x");
exact_expr expression = pow(cas.integer(1) + sqrt(cas.integer(2)) + x,
                            cas.integer(123));
```

The power remains a single power node. Ordinary construction never expands it
into a large sum.

Approximate values retain `Number`'s precision metadata. Mixed arithmetic
promotes exact operands to the approximate operand's precision, while purely
integer and rational operations remain exact. Interning compares the stored
approximate bits and precision rather than using fuzzy equality.

## Sharing and Canonicalization

Nodes are immutable and hash-consed. Constructing `cas.integer(2)` repeatedly
returns the same node ID. Addition and multiplication are n-ary, flattened,
constant-folded, sorted, and interned, so operand order does not change the
resulting expression. Subtraction combines signed coefficients, while division
uses negative integer powers and combines exponents. Consequently `x-x`
becomes `0`, `x/x` becomes `1`, and `x^2/x^3` becomes `x^-1`.

The arena uses fixed-size nodes plus a contiguous array of 32-bit operand IDs.
The operands refer to shared nodes; they do not own contiguous subtrees.

## Large Numeric Sums

Use a transient builder when parsing a long addition:

```cpp
exact_add_builder sum = cas.make_add_builder();
for(uint64_t i = 1; i <= 10000000; ++i) sum.add_integer(i);
exact_expr result = sum.finish();
```

Small positive and negative literals first use 64-bit accumulators and spill
to the big integer only on overflow, so this creates one final integer node
rather than ten million temporary nodes or big-integer allocations. Generated sums can use
`bounded_sum`; the initial implementation recognizes `sum(i, i=lower..upper)`
and evaluates it with the arithmetic-series formula.

## Current Scope

This foundation handles exact constants, symbols, canonical addition and
multiplication, compact powers, square roots of perfect rational squares, and
bounded sums. General expansion, substitution, differentiation, parsing, and
garbage collection should be added on top of this representation rather than
changing its public handles.
