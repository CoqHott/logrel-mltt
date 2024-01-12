# A Logical Relation for Observational Equality Meets CIC #

This is a formal proof of the decidability of conversion for a fragment of the theory CICobs, which
extends the calculus of inductive constructions (CIC) with an equality satisfying UIP, function
extensionality, proposition extensionality, and which preserves the computation rule of Martin-Löf's
identity type.

The source code can be browsed in HTML [here](https://htmlpreview.github.io/?https://github.com/CoqHott/logrel-mltt/blob/impredicativity-cast-compute-refl/html/README.html).

### CIC with an observational equality ###

The type theory under scrutiny is a simplified version of CIC<sup>obs</sup>, as described in the
companion paper.

It features:
- A hierarchy of universes for proof-relevant types
- An impredicative universe of proof-irrelevant types,
- dependent products, with domain and codomain in any universe,
- dependent pairs with proof-irrelevant domain and codomain ("existential types"),
- proof-irrelevant identity types and type casting along equalities in the universes,
- a conversion rule for simplifying type-casts along a reflexive equality
- natural numbers and a proof-irrelevant empty type.
However, it is subject to the following restrictions:
- The universe hierarchies are restricted to two levels,
- no general inductive types,
- no quotient types.

The interested reader is invited to consult either the companion paper for a more precise but still
high-level account of CIC<sup>obs</sup>, or the formal proof for a complete definition.

### New features of the proof ###

Compared to the reducibility proof for CC<sup>obs</sup> from the paper "Impredicative Observational
Equality" of Pujet and Tabareau, the main difference is a new conversion rule for cast along
reflexive equalities:
```
A ≡ B  ⊢  cast A B e t ≡ t   (*)
```
Rule (\*) has a convertibility premise, which makes it difficult to incorporate in the reduction
strategy. Instead, rule (\*) is handled in a similar manner to eta-conversion, in that it only
appears at conversion checking.

Another difference with CC<sup>obs</sup> is that the observational equality does not reduce anymore.
Instead, the theory is equipped with primitive operators that turn an observational equality between
two dependent products into an equality between their domains and codomains.
See the companion paper for more information on this.

### Structure of the proof ###

The raw, untyped syntax is defined inductively, followed by an inductive definition of the typing
derivations of CIC<sup>obs</sup>.

The proof then relies on Agda's implementation of induction-recursion to define a logical relation
that characterizes the computational behaviour of the typing judgments. The logical relation is more
or less the same as the logical relation from "Impredicative Observational Equality".
Some basic properties of this logical relation are then established, in order to prove the
*fundamental lemma*, which states that any derivable judgement satisfies the logical relation.

Once the fundamental lemma has been proven, it entails several fundamental properties of the type
theory, such as the termination of the weak-head reduction strategy, the canonicity of the integers,
typing inversion results, etc.
Note that because there is no computation in the impredicative logical layer, canonicity follows
from consistency, which has to be proven externally using a model.

This first part lays the foundation necessary to the definition of an algorithmic equality relation
on types and terms. We can prove that this algorithmic equality is decidable, and, using the
fundamental lemma, that it coincides with the judgmental equality.
This algorithmic equality is the main contribution of this work: because of rule (\*), the
algorithmic equality must simplify away the typecasts on proofs by reflexivity, which involves
some amount of backtracking.

A more detailed, but still high-level overview of the proof is provided in the companion paper.

### Files ###

A more detailed description of the role of each file can be found in README.agda

### Dependencies ###

This project is written in Agda. It has been tested to be working with Agda version 2.6.3.

### Warning ###

The reader who wishes to type-check the entire proof should be warned that some files may
be quite resource-intensive (Some will take more than 10 minutes on a higher end laptop).
The main culprits are the following:

- Typed.Properties (medium)
- LogicalRelation.Substitution.Introductions.Natrec (medium)
- LogicalRelation.Substitution.Introductions.CastLemmas (medium)
- LogicalRelation.Substitution.Introductions.Cast (long)
- LogicalRelation.Substitution.Introductions.CastRefl (medium)
- Conversion.TransitivityHelper (long)
- Conversion.Transitivity (long)
- Conversion.DecidableLemmas (long)
- Conversion.DecView (very long)
- Conversion.Decidable (very long)