# A Logical Relation for Impredicative Observational Equality in Agda #

This is a formalized proof of decidability of conversion for an impredicative
implementation of observational type theory.

Compared to [previous work](https://github.com/CoqHott/logrel-mltt/tree/setoid-universes-hierarchy),
the hierarchy of universes Prop_i is replaced by a single universe Prop. This universe
allows *impredicative* quantification, meaning that it is closed under dependent products
indexed over arbitrarily large types.
The observational equality is defined in Prop, and supports large elimination through 
type-casting. This shows that impredicativity is compatible with a definitionally 
proof-irrelevant equality.

The source code can be browsed in HTML [here](https://htmlpreview.github.io/?https://github.com/CoqHott/logrel-mltt/blob/impredicativity-SProp-POPL/html/README.html).

### Impredicative Observational Equality ###

The type theory under scrutiny is a simplified version of CC<sup>obs</sup>, as described in the companion
paper.
It features:
- A hierarchy of universes for proof-relevant types
- An single impredicative universe for proof-irrelevant types,
- dependent products, with domain and codomain in any universe,
- dependent pairs with proof-irrelevant domain and codomain ("existential types"),
- proof-irrelevant identity types and type casting along equalities in the universes,
- natural numbers and a proof-irrelevant empty type.
- 
However, it is subject to the following restrictions:
- The universe hierarchies are restricted to two levels,
- no general inductive types,
- no equality types à la Swan,
- no quotient types.

The interested reader is invited to consult either the companion paper or the formalized definitions
for a more detailed account of CC<sup>obs</sup>.

### Structure of the proof ###

The raw, untyped syntax is defined inductively, followed by an inductive definition of the typing
derivations of CC<sup>obs</sup>.
 
The proof then relies on Agda's implementation of induction-recursion to define a logical relation
that characterizes the computational behaviour of the typing judgments. Some basic properties of
this logical relation are then established, in order to prove the *fundamental lemma*, which states
that any derivable judgement satisfies the logical relation.

The main innovation compared to [the normalisation proof of Abel et al.](https://github.com/mr-ohman/logrel-mltt/) 
and [the normalisation proof for TT<sup>obs</sup>](https://github.com/CoqHott/logrel-mltt/tree/setoid-universes-hierarchy) 
is the fact that the reducibility predicate for the impredicative universe does not depend on type reducibility, which
allows us to define it upfront.

Once the fundamental lemma has been proven, it entails several fundamental properties of the type
theory, such as the termination of the weak-head reduction strategy, the canonicity of the integers,
typing inversion results, etc.

This first part lays the foundation necessary to the definition of an algorithmic equality relation
on types and terms. We can prove that this algorithmic equality is decidable, and, using the
fundamental lemma, that it coincides with the judgmental equality. It follows that the judgmental
equality of terms and types is decidable.

Note that because there is no computation in the impredicative logical
layer, canonicity follows from consistency, which has to be proven
externally using a model. 

A more detailed, but still high-level overview of the proof is provided in the companion paper.

### Files ###

A more detailed description of the role of each file can be found in README.agda

### Dependencies ###

This project is written in Agda. It has been tested to be working with Agda version 2.6.3.

### Warning ###

The reader who wishes to type-check the entire proof should be warned that the files
Defintion/LogicalRelations/Substitution/Introductions/Cast.agda and Conversion/Decidable.agda may
be quite resource-intensive (Type-checking the latter seems to take at least 10 min on a
higher-end laptop).
