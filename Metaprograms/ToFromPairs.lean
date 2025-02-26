/-
Copyright (c) 2025 Lean FRO, LLC. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Lean

/-!
2025-02-26

For which ordered pairs of types `(X, Y)` does there exist a `X.toY` function, a `Y.ofX` function
or both?
-/

open Lean Meta

def blub : MetaM Unit := do
  let env ← getEnv
  let mut pairs : Array (String × String) := #[]
  let mut ofNames : Array String := #[]
  let mut toNames : Array String := #[]
  for (name, info) in env.constants do
    if info.isTheorem then
      continue
    if (`Lean).isPrefixOf name || (`_private).isPrefixOf name then
      continue
    let Name.str (Name.str inner n) s := name | continue
    if let some t := s.dropPrefix? "of" then
      let otherName := Name.str (Name.str inner t.toString) ("to" ++ n)
      if env.contains otherName then
        pairs := pairs.push (name.toString, otherName.toString)
      else
        ofNames := ofNames.push name.toString
    else if s.startsWith "to" then
      toNames := toNames.push name.toString

  have : Ord (String × String) := lexOrd
  pairs := pairs.qsortOrd
  ofNames := ofNames.qsort
  toNames := toNames.qsort

  for n in pairs do
    IO.println n
  for n in ofNames ++ toNames do
    IO.println n

-- #eval blub
