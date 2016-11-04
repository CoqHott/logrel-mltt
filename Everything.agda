module Everything where

import Tools.Context

import Definition.Untyped
import Definition.Untyped.Indexed
import Definition.Untyped.Properties

import Definition.Typed
import Definition.Typed.Properties
import Definition.Typed.Weakening
-- import Definition.Typed.Arrows     -- unsolved metas

import Definition.LogicalRelation
import Definition.LogicalRelation.Tactic
import Definition.LogicalRelation.Irrelevance
import Definition.LogicalRelation.Weakening
import Definition.LogicalRelation.Properties

import Definition.LogicalRelation.Substitution
import Definition.LogicalRelation.Substitution.Properties
import Definition.LogicalRelation.Substitution.Irrelevance
import Definition.LogicalRelation.Substitution.Conversion
import Definition.LogicalRelation.Substitution.Reduction
import Definition.LogicalRelation.Substitution.Reflexivity
import Definition.LogicalRelation.Substitution.Weakening
import Definition.LogicalRelation.Substitution.Introductions

import Definition.LogicalRelation.Fundamental
import Definition.LogicalRelation.Consequences.Canonicity
import Definition.LogicalRelation.Consequences.Injectivity
import Definition.LogicalRelation.Consequences.SingleSubst
import Definition.LogicalRelation.Consequences.Inversion
