{-# OPTIONS --safe #-}

module README where

-- Formalization of the decidability of conversion for a fragment of CICobs
-- Git repository: https://github.com/CoqHott/logrel-mltt/tree/impredicativity-cast-compute-refl


------------------
-- INTRODUCTION --
------------------

-- A minimal library necessary for formalization:

-- The empty type and its elimination rule.
import Tools.Empty

-- The unit type.
import Tools.Unit

-- Disjoint sum type.
import Tools.Sum

-- Products and Sigma-types.
import Tools.Product

-- Identity function and composition.
import Tools.Function

-- Negation and decidability type.
import Tools.Nullary

-- Propositional equality and its properties.
import Tools.PropositionalEquality

-- Natural numbers and decidability of equality.
import Tools.Nat

-- Lists definition
import Tools.List

-- Proof by reflection for a family of integer inequalities
-- This is used later on to prove that an induction is well-founded:
-- we need to show that the size of the argument decreases with each recursive call
import Tools.Inequality

---------------------------
-- LANGUAGE INTRODUCTION --
---------------------------

-- Syntax and semantics of weakening and substitution.
import Definition.Untyped

-- Propositional equality properties: Equalities between expressions,
-- weakenings, substitutions and their combined composition.
import Definition.Untyped.Properties

-- Judgements: Typing rules, conversion, reduction rules
-- and well-formed substitutions and respective equality.
-- The conversion rule cast-refl is the main contribution of this development.
import Definition.Typed

-- Well-formed context extraction and reduction properties.
import Definition.Typed.Properties

-- Well-formed weakening and its properties.
import Definition.Typed.Weakening


------------------------------
-- KRIPKE LOGICAL RELATIONS --
------------------------------

-- Generic equality relation definition.
import Definition.Typed.EqualityRelation

-- The judgemental instance of the generic equality.
import Definition.Typed.EqRelInstance

-- Logical relations definitions.
import Definition.LogicalRelation

-- Properties of logical relation:

-- Reflexivity of the logical relation.
import Definition.LogicalRelation.Properties.Reflexivity

-- Escape lemma for the logical relation.
import Definition.LogicalRelation.Properties.Escape

-- Shape view of two or more types.
import Definition.LogicalRelation.ShapeView

-- Proof irrelevance for the logical relation.
import Definition.LogicalRelation.Irrelevance

-- Weakening of logical relation judgements.
import Definition.LogicalRelation.Weakening

-- Conversion of the logical relation.
import Definition.LogicalRelation.Properties.Conversion

-- Symmetry of the logical relation.
import Definition.LogicalRelation.Properties.Symmetry

-- Transitvity of the logical relation.
import Definition.LogicalRelation.Properties.Transitivity

-- Neutral introduction in the logical relation.
import Definition.LogicalRelation.Properties.Neutral

-- Weak head expansion of the logical relation.
import Definition.LogicalRelation.Properties.Reduction

-- Application in the logical relation.
import Definition.LogicalRelation.Application

-- Validity judgements definitions
import Definition.LogicalRelation.Substitution

-- Properties of validity judgements:

-- Proof irrelevance for the validity judgements.
import Definition.LogicalRelation.Substitution.Irrelevance

-- Properties about valid substitutions:
-- * Substitution well-formedness.
-- * Substitution weakening.
-- * Substitution lifting.
-- * Identity substitution.
-- * Reflexivity, symmetry and transitivity of substitution equality.
import Definition.LogicalRelation.Substitution.Properties

-- Single term substitution of validity judgements.
import Definition.LogicalRelation.Substitution.Introductions.SingleSubst

-- The fundamental theorem.
import Definition.LogicalRelation.Fundamental

-- Certain cases of the fundamental theorem

-- Validity of the universes
import Definition.LogicalRelation.Substitution.Introductions.Universe

-- Validity of the empty type and its eliminator
import Definition.LogicalRelation.Substitution.Introductions.Empty
import Definition.LogicalRelation.Substitution.Introductions.Emptyrec

-- Validity of natural numbers and its eliminator
import Definition.LogicalRelation.Substitution.Introductions.Nat
import Definition.LogicalRelation.Substitution.Introductions.Natrec

-- Validity of Π-types, abstractions and applications
import Definition.LogicalRelation.Substitution.Introductions.Pi
import Definition.LogicalRelation.Substitution.Introductions.Application
import Definition.LogicalRelation.Substitution.Introductions.Lambda

-- Validity of ∃-types, pairs and projections
import Definition.LogicalRelation.Substitution.Introductions.Fst
import Definition.LogicalRelation.Substitution.Introductions.Snd

-- Validity of type casting and proof-irrelevant transport
import Definition.LogicalRelation.Substitution.Introductions.Castlemmas
import Definition.LogicalRelation.Substitution.Introductions.Cast
import Definition.LogicalRelation.Substitution.Introductions.CastPi
import Definition.LogicalRelation.Substitution.Introductions.Transp

-- Validity of identity types, and reflexivity
import Definition.LogicalRelation.Substitution.Introductions.Id
import Definition.LogicalRelation.Substitution.Introductions.IdRefl

-- Reducibility of well-formedness.
import Definition.LogicalRelation.Fundamental.Reducibility

-- Consequences of the fundamental theorem:

-- Consistency (no proof of False in the empty context) implies
-- canonicity of the system.
import Definition.Typed.Consequences.Canonicity

-- Injectivity of Π-types.
import Definition.Typed.Consequences.Injectivity

-- Syntactic validitiy of the system.
import Definition.Typed.Consequences.Syntactic

-- All types and terms fully reduce to WHNF.
import Definition.Typed.Consequences.Reduction

-- Strong equality of types.
import Definition.Typed.Consequences.Equality

-- Syntactic inequality of types.
import Definition.Typed.Consequences.Inequality

-- Substitution in judgements and substitution composition.
import Definition.Typed.Consequences.Substitution

-- Uniqueness of the types of neutral terms.
import Definition.Typed.Consequences.NeTypeEq

-- Consistency (0 is not judgementally equal to 1) of the type theory.
import Definition.Typed.Consequences.Consistency

-- Types can only belong to one universe (because of annotations)
-- also various inequalities for conversion
import Definition.Typed.Consequences.PiNorm
import Definition.Typed.Consequences.RelevanceUnicity

-- Terms can only admit one type
import Definition.Typed.Consequences.TypeUnicity

-- Various inversion results
import Definition.Typed.Consequences.TypeUnicity

------------------
-- DECIDABILITY --
------------------

-- Conversion algorithm definition.
import Definition.Conversion

-- A size measure for conversion proofs
-- Because of cast-refl, some proofs cannot be done by structural induction
-- For these, we will show that they terminate by induction on the size of
-- the derivation of algorithmic conversion
import Definition.Conversion.ConvSize

-----------------------------------------
-- Properties of conversion algorithm: --
-----------------------------------------

-- Context equality and its properties:
-- * Context conversion of typing judgements.
-- * Context conversion of reductions and algorithmic equality.
-- * Reflexivity and symmetry of context equality.
import Definition.Conversion.Stability

-- Soundness of the conversion algorithm.
import Definition.Conversion.Soundness

-- Weakening of the conversion algorithm.
import Definition.Conversion.Weakening

-- The type of the conversion algorithm is stable under definitional equality
import Definition.Conversion.Conversion

-- Transitivity of the conversion algorithm.
import Definition.Conversion.Transitivity

-- Symmetry of the conversion algorithm.
import Definition.Conversion.Symmetry

-- Symmetry does not change the size of the derivation
import Definition.Conversion.SymmetrySize

-- Conversion is an instance of the generic equality relation interface
import Definition.Conversion.EqRelInstance

-- Completeness of conversion algorithm.
import Definition.Conversion.Consequences.Completeness

-- Results around normalisation of reflexive terms
import Definition.Conversion.FullReduction

-------------------------------------------
-- Decidability of conversion algorithm: --
-------------------------------------------

-- Useful lemmas for the decidability proof
import Definition.Conversion.HelperDecidable
import Definition.Conversion.DecidableLemmas
import Definition.Conversion.DecView

-- Decidability of the conversion algorithm.
import Definition.Conversion.Decidable

-- Generic equality relation instance for the conversion algorithm.
import Definition.Conversion.EqRelInstance

-- Decidability of judgemental conversion.
import Definition.Conversion.HelperDecidable
import Definition.Typed.Decidable

--------------------------------
-- BONUS: NON-PARANOID TYPING --
--------------------------------

-- The typing rules in Definition.Typed have unnecessary premises
-- Now that we know a lot about the properties of the theory, we can give
-- an alternative and less verbose presentation of the theory
import Definition.Typed.NonParanoidTyping

-- Likewise, we can do the same for the algorithmic equality, to simplify
-- the conversion checking algorithm
import Definition.ConversionGen
import Definition.Conversion.ConversionGenEquiv
