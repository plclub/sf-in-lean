import SFLMeta.BuildStamp

def main : IO Unit := do
  IO.println (← SFLMeta.computeBuildStamp)
