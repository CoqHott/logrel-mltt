{-# OPTIONS --without-K #-}

module README where


------------------
-- INTRODUCTION --
------------------

-- A minimal library necessary for formalization:

-- The empty type and its elimination rule.
import Tools.Empty

-- The unit type.
import Tools.Unit

-- Sum type.
import Tools.Sum

-- Product type.
import Tools.Product

-- Negation and decidability type.
import Tools.Nullary

-- Propositional equality and its properties.
import Tools.PropositionalEquality

-- Natural numbers and decidability of equality.
import Tools.Nat


---------------------------
-- LANGUAGE INTRODUCTION --
---------------------------

-- Syntax and semantics of weakening and substitution.
import Definition.Untyped

-- Propositional equality properties: Equalities between expressions,
-- weakenings, substitutions and their combined composition.
-- (omitted from paper)
import Definition.Untyped.Properties

-- Judgements: Typing rules, conversion and reduction rules.
import Definition.Typed

-- Well-formed context extraction and reduction properties.
import Definition.Typed.Properties

-- Well-formed weakening and its properties.
import Definition.Typed.Weakening

import Definition.Typed.Reduction -- (not in paper yet)

import Definition.Typed.RedSteps -- (not in paper yet)


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
import Definition.LogicalRelation.Properties.Wellformed

-- Equality view of two or more types.
import Definition.LogicalRelation.Tactic

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

-- Universe introduction in the logical relation.
import Definition.LogicalRelation.Properties.Universe

-- Successor of natural numbers in the logical relation.
import Definition.LogicalRelation.Properties.Successor

import Definition.LogicalRelation.Properties.MaybeEmb -- (not in paper yet)

-- Validity judgements definitions
import Definition.LogicalRelation.Substitution

-- Properties of validity judgements:

-- Proof irrelevance for the validity judgements.
import Definition.LogicalRelation.Substitution.Irrelevance

-- Properties about valid substitutions:
-- * Substitution weakening.
-- * Substitution lifting.
-- * Identity substitution.
-- * Reflexivity, symmetry and transitivity of substitution equality.
import Definition.LogicalRelation.Substitution.Properties

-- Single term substitution of validity judgements.
import Definition.LogicalRelation.Substitution.Introductions.SingleSubst

-- Validity of Π-types.
import Definition.LogicalRelation.Substitution.Introductions.Pi

-- Validity of applications.
import Definition.LogicalRelation.Substitution.Introductions.Application

-- Validity of λ-terms.
import Definition.LogicalRelation.Substitution.Introductions.Lambda

-- Validity of natural recursion of natural numbers.
import Definition.LogicalRelation.Substitution.Introductions.Natrec

-- (These do not appear in the paper, as they are valid variants of sound lemmas
--  or minor helping lemmas)
import Definition.LogicalRelation.Substitution.Conversion
import Definition.LogicalRelation.Substitution.Reduction
import Definition.LogicalRelation.Substitution.Reflexivity
import Definition.LogicalRelation.Substitution.Weakening
import Definition.LogicalRelation.Substitution.Soundness
import Definition.LogicalRelation.Substitution.Wellformed
import Definition.LogicalRelation.Substitution.MaybeEmbed
import Definition.LogicalRelation.Substitution.Introductions.Nat
import Definition.LogicalRelation.Substitution.Introductions.Universe

-- The fundamental theorem.
import Definition.LogicalRelation.Fundamental

-- Consequences of the fundamental theorem:

-- Canonicity of the system.
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

-- Substiution in judgements and substitution composition.
import Definition.Typed.Consequences.Substitution

-- Uniqueness of the types of neutral terms.
import Definition.Typed.Consequences.NeTypeEq

-- Universe membership of types.
import Definition.Typed.Consequences.InverseUniv

import Definition.Typed.Consequences.SucCong -- (not in paper yet)

import Definition.Typed.Consequences.Inversion -- (not in paper yet)

------------------
-- DECIDABILITY --
------------------

-- Conversion algorithm definition.
import Definition.Conversion

-- Properties of conversion algorithm:

-- Context equality and its properties:
-- * Context conversion of typing judgements.
-- * Context conversion of reductions and algorithmic equality.
-- * Reflexivity and symmetry of context equality.
import Definition.Conversion.Stability

-- Soundness of the conversion algorithm.
import Definition.Conversion.Soundness

-- Conversion property of algorithmic equality.
import Definition.Conversion.Conversion

-- Decidability of the conversion algorithm.
import Definition.Conversion.Decidable

-- Symmetry of the conversion algorithm.
import Definition.Conversion.Symmetry

-- Transitivity of the conversion algorithm.
import Definition.Conversion.Transitivity

-- Weakening of the conversion algorithm.
import Definition.Conversion.Weakening

-- WHNF and neutral lifting of the conversion algorithm.
import Definition.Conversion.Lift

import Definition.Conversion.Reduction -- (not in paper yet)

import Definition.Conversion.Universe -- (not in paper yet)

import Definition.Conversion.Whnf -- (not in paper yet)

-- Generic equality relation instance for the conversion algorithm.
import Definition.Conversion.EqRelInstance

-- Completeness of conversion algorithm.
import Definition.Conversion.Consequences.Completeness

-- Decidability of judgemental conversion.
import Definition.Typed.Decidable
