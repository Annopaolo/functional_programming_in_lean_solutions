def main : IO Unit := do
  -- This binds the IO value to englishGreeting (it is :=, not <-)
  let englishGreeting := IO.println "Hello!"
  IO.println "Bonjour!"
  -- this runs the actual englishGreeting
  englishGreeting
