module

public import Glorious.Check.Program
public import Glorious.Check.Written

/-!
# Type and effect inference

Checks a program before it is elaborated. Types and effects are inferred:
annotations on functions are optional, and a field of a data or operation
declaration written as a bare name has its type inferred from how the program
uses it. A declaration with type parameters is polymorphic; one with inferred
fields has a single type throughout the program.

The checker establishes that values are used at consistent types, that calls
supply the right number of arguments, that pattern clauses cover every case,
that every effect a program performs is handled before it reaches `main`, that
no callable able to jump to a label can be called after the label's scope has
ended, that nothing able to reach a mutable variable outlives the block the
variable is declared in, that a variable is not used against a borrow of it
that is still held, and that nothing holding a resumption is used more than
once. This pass is not proved.

A trait's function is used at a type that has the trait. Which implementation
a use needs is found by `Traits.solve`, which is proved to find only evidence
that the bound is met, and evidence that is the only evidence there is.
-/

public section
