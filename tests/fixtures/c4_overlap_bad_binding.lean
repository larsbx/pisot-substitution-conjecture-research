import PscVerif.OverlapPacket

/- A standard-axiom module with misleading proof names and an unrelated emitter.
   The independent audit must reject the proof types before emitting data. -/
namespace PscVerif.OverlapGenerated.Source0

def packet := PscVerif.OverlapPacket.terminalControl

theorem accepted : True := True.intro

theorem typed_accepted : True := True.intro

def emit : IO Unit := IO.println "unrelated packet output"

end PscVerif.OverlapGenerated.Source0
