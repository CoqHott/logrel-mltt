{-# OPTIONS --safe #-}

module README where

-- Formalization for "Decidability of Conversion for Type Theory in Type Theory"
-- Git repository: https://github.com/mr-ohman/logrel-mltt


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

-- Identity function and composition.
import Tools.Function

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
-- (These lemmas are not in the paper.)
import Definition.Untyped.Properties

-- Judgements: Typing rules, conversion, reduction rules
-- and well-formed substitutions and respective equality.
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

-- Certain cases of the logical relation:

-- Validity of Π-types.
import Definition.LogicalRelation.Substitution.Introductions.Pi

-- Validity of applications.
import Definition.LogicalRelation.Substitution.Introductions.Application

-- Validity of λ-terms.
import Definition.LogicalRelation.Substitution.Introductions.Lambda

-- Validity of natural recursion of natural numbers.
import Definition.LogicalRelation.Substitution.Introductions.Natrec


-- Reducibility of well-formedness.
import Definition.LogicalRelation.Fundamental.Reducibility

-- Consequences of the fundamental theorem:

-- Canonicity of the system.
--import Definition.Typed.Consequences.Canonicity

