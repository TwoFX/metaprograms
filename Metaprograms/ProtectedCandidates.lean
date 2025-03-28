/-
Copyright (c) 2025 Lean FRO, LLC. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Lean

/-!
Which names defined in the namespaces for bounded integers are also defined in a different
namespace? These might be good candidates for a `protected` annotation.
-/

open Lean

def boundedIntNamespaces : NameSet :=
  .ofList [``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize, ``Int8, ``Int16, ``Int32, ``Int64, ``ISize]

def search : MetaM Unit := do
  let env ← getEnv
  let mut map : Std.HashMap String (Array Name) := ∅
  for (n, _) in env.constants do
    let .str l r := n | continue
    map := map.alter r (fun o => some ((o.getD #[]).push l))

  for (k, v) in map do
    if v.all boundedIntNamespaces.contains then continue
    if v.all (Bool.not ∘ boundedIntNamespaces.contains) then continue
    IO.println s!"{k} {(v.filter (Bool.not ∘ boundedIntNamespaces.contains)).take 5}"

  return ()
