{-# OPTIONS --safe #-}

-- A Logical Relation for Dependent Type Theory Formalized in Agda

module Everything where

-- README
import README

-- Minimal library
import Tools.Empty
import Tools.Unit
import Tools.Nat
import Tools.Sum
import Tools.Product
import Tools.Function
import Tools.Nullary
import Tools.List
import Tools.PropositionalEquality

-- Grammar of the language
import Definition.Untyped
import Definition.Untyped.Properties

-- Typing and conversion rules of language
import Definition.Typed
import Definition.Typed.Properties
import Definition.Typed.Weakening
import Definition.Typed.Reduction
import Definition.Typed.RedSteps
import Definition.Typed.EqualityRelation
import Definition.Typed.EqRelInstance

-- Logical relation
import Definition.LogicalRelation
import Definition.LogicalRelation.ShapeView
import Definition.LogicalRelation.Irrelevance
import Definition.LogicalRelation.Weakening
import Definition.LogicalRelation.Properties
import Definition.LogicalRelation.Application

import Definition.LogicalRelation.Substitution
import Definition.LogicalRelation.Substitution.Properties
import Definition.LogicalRelation.Substitution.Irrelevance
import Definition.LogicalRelation.Substitution.Conversion
import Definition.LogicalRelation.Substitution.Reduction
import Definition.LogicalRelation.Substitution.Reflexivity
import Definition.LogicalRelation.Substitution.Weakening
import Definition.LogicalRelation.Substitution.Reducibility
import Definition.LogicalRelation.Substitution.Escape
import Definition.LogicalRelation.Substitution.MaybeEmbed
import Definition.LogicalRelation.Substitution.Introductions

import Definition.LogicalRelation.Fundamental
import Definition.LogicalRelation.Fundamental.Reducibility

-- Consequences of the logical relation for typing and conversion
import Definition.Typed.Consequences.Canonicity
