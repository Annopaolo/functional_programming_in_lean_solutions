/-!
# Two

Solution to the `IO` exercise: an `IO` action bound with `let` is not run until it is used.
-/

namespace HelloWorld

def main : IO Unit := do
  -- This binds the IO value to englishGreeting (it is :=, not <-)
  let englishGreeting := IO.println "Hello!"
  IO.println "Bonjour!"
  -- this runs the actual englishGreeting
  englishGreeting

end HelloWorld
