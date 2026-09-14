/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Network.IndexCoding

namespace CapacityAtlas.IndexCoding

/-- Receiver r knows only its successor. The cycle has k+3 messages. -/
@[capacity_problem "directed-cycle-index-coding", capacity_definition]
def directedCycle (k : ℕ) : Instance (Fin (k + 3)) (Fin (k + 3)) :=
  Instance.fromInterference id (fun r ↦ Finset.univ \ {r, r + 1})

/-- Receiver r knows the two adjacent messages of the undirected five-cycle. -/
@[capacity_problem "five-cycle-index-coding", capacity_definition]
def undirectedFiveCycle : Instance (Fin 5) (Fin 5) :=
  Instance.fromInterference id (fun r ↦ Finset.univ \ {r, r + 1, r - 1})

end CapacityAtlas.IndexCoding
