/-
Copyright (c) 2025 Lean FRO, LLC. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Lean
import Std

/-!
Which `simp` lemmas contain both `Nat.cast n` and `n` on the LHS?
-/

namespace NonLinearNatCastSimpLemmas

open Lean Meta

def isSimpTheorem (name : Name) : MetaM Bool := do
  let simpTheorems ← getSimpTheorems
  return simpTheorems.lemmaNames.contains (.decl name)

def fVarsInsideNatCast (e : Expr) : Std.HashSet FVarId :=
  match e with
  | .app (.app (.app (.const `Nat.cast _) _) _) (.fvar id) => { id }
  | .app lhs rhs =>
    let left := fVarsInsideNatCast lhs
    let right := fVarsInsideNatCast rhs
    left.union right
  | .lam _ _ body _ | .forallE _ _ body _ => fVarsInsideNatCast body
  | .letE .. => panic! s!"Unhandled case: {e}"
  | _ => ∅

def fVarsNotInsideNatCast (e : Expr) : Std.HashSet FVarId :=
  if e.isAppOf `Nat.cast then ∅ else
  match e with
  | .app lhs rhs =>
    let left := fVarsNotInsideNatCast lhs
    let right := fVarsNotInsideNatCast rhs
    left.union right
  | .fvar id => { id }
  | .lam _ _ body _ | .forallE _ _ body _ => fVarsNotInsideNatCast body
  | .letE .. => panic! s!"Unhandled case: {e}"
  | _ => ∅

def isBadLHS (e : Expr) : MetaM Bool := do
  let inside := fVarsInsideNatCast e
  let notInside := fVarsNotInsideNatCast e
  return inside.any notInside.contains

partial def stripMData : Expr → Expr :=
  Expr.replace (fun | .mdata _ e => some (stripMData e) | _ => none)

def isBadTheorem (c : ConstantInfo) : MetaM Bool := do
  unless c.type.getUsedConstants.contains `Nat.cast do return false
  let ty := stripMData c.type
  let depth := ty.getNumHeadForalls
  let fvars ← Array.range depth |>.mapM (fun _ => return .fvar (← mkFreshFVarId))
  let transformedType ← instantiateForall ty fvars
  -- println! "{transformedType}"
  match_expr transformedType with
  | Eq _ lhs _ => isBadLHS lhs
  | _ => return false

def search : MetaM Unit := do
  let env ← getEnv
  let mut ans : Array String := #[]
  for (name, info) in env.constants do
    let isSimpThm ← isSimpTheorem name
    unless isSimpThm do continue
    let isBadThm ← isBadTheorem info
    unless isBadThm do continue
    ans := ans.push ((← Lean.PrettyPrinter.ppSignature name).fmt.pretty)
  ans := ans.qsort
  for a in ans do
    println! "{a}"

-- #eval search
