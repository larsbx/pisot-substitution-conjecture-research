import PscVerif.ArchivedPayloadConsumer

/- This deliberate negative fixture is not a mathematical acceptance proof.
The names are right and every declaration is harmless, but the types are wrong. -/
namespace Psc.ArchivedPayloadGenerated.Source0

def packet : Psc.ArchivedPayload.Packet where
  fixture := 0
  count := 7150
  table := .empty
  index := .empty
  power := 2
  boxX := 16
  boxY := 8
  direction := 0
  numerator := 99
  residueRejections := 0
  boxRejections := 0
  edges := 0
  swapped := 0
  repeated := 0
  maxDepth := 0
  sweeps := 0
  minimumGap := 0

theorem valid : True := True.intro
theorem accepted : True := True.intro
theorem typed_accepted : True := True.intro
theorem domain_iff : True := True.intro
theorem roots_null : True := True.intro
theorem ancestors_null : True := True.intro
theorem no_strict_system (_ : Finset Psc.OccurrenceTransport.WordPair) : True := True.intro

end Psc.ArchivedPayloadGenerated.Source0
