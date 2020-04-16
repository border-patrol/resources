# Resources: A framework for Resource Dependent EDSLs in Idris.

Resources is framework for creating Resource Dependent EDSLs as described in the 2020 ECOOP paper: *A Framework for Resource Dependent EDSLs in a Dependently Typed Language*.

Idris’ Effects library demonstrates how to embed resource dependent algebraic effect handlers into a dependently-typed host language, providing runtime and compile-time based reasoning on type-level resources.
Building upon this work, Resources is a framework for realising Embedded Domain Specific Languages (EDSLs) with type-systems that contain domain specific substructural properties. Differing from Effects, Resources allows a language’s substructural properties to be encoded in a resource that is associated with language variables.
Such an association allows for multiple effect instances to be reasoned about autonomically and without explicit type-level declaration. Type-level predicates are used as proof that the language’s substructural properties hold.
Several exemplar EDSLs are presented that illustrates our framework’s operation and how dependent types provide correctness-by-construction guarantees that substructural properties of written programs hold.
