import Lean
open Lean Meta

/--
A custom environment extension to add a theorem name, and its type.
We store these pairs (expr, type) in a simple Array.
-/
initialize myExt :
    SimpleScopedEnvExtension (Expr × Expr) (Array (Expr × Expr)) ←
  registerSimpleScopedEnvExtension {
    -- add a single element to the array
    addEntry := fun arr et => arr.push et
    -- initially, the array is empty
    initial := #[]
  }

/--
Custom attribute `my_tag` adding a theorem to the `myExt`
-/
initialize registerBuiltinAttribute {
  name := `my_tag
  descr := "a custom tag"
  -- by default, assigning an attribute runs in CoreM
  -- but we can invoke MetaM, if we need
  add := fun name stx kind ↦ MetaM.run' do
    -- We assume we are only registering theorems without universe levels,
    -- Making it work with universe levels is left as an exercise.
    let e : Expr := mkConst name
    let t : Expr ← inferType e
    myExt.add (e,t) -- calling `addEntry` we defined in `myExt`

    -- For simplicity, we are also omiting a sanity check. Usually
    -- you should also check here if the tagged definition makes sense
    -- for the particular attribute before adding it to the database.
}
