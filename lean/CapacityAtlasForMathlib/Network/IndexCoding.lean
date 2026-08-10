/-
Copyright 2026 The Capacity Atlas Authors

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import CapacityAtlasUtil.Metadata
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace CapacityAtlas.IndexCoding

/-- A multiple-unicast index-coding instance.

Receiver `i` requests message `i`. `interference i` contains the messages that
receiver `i` neither requests nor knows as side information.
-/
@[capacity_shared_api]
structure Instance (messageCount : ℕ) where
  interference : Fin messageCount → Finset (Fin messageCount)
  self_not_interference : ∀ receiver, receiver ∉ interference receiver

namespace Instance

/-- Messages available as side information at a receiver. -/
@[capacity_shared_api]
def sideInformation {messageCount : ℕ} (problem : Instance messageCount)
    (receiver : Fin messageCount) : Finset (Fin messageCount) :=
  (Finset.univ.erase receiver) \ problem.interference receiver

end Instance

/-- The interference sets in the 11-message Sun--Jafar index-coding instance.

The zero-based rows encode
`{4,5}, {5}, ∅, ∅, {2}, {2,3}, {1,3}, {2,4}, {3,4}, {3,5}, {4,6}`
in the one-based notation used in the paper.
-/
@[capacity_problem "sun-jafar-11-message-index-coding", capacity_definition]
def sunJafar11Interference : Fin 11 → Finset (Fin 11) :=
  ![
    {3, 4},
    {4},
    ∅,
    ∅,
    {1},
    {1, 2},
    {0, 2},
    {1, 3},
    {2, 3},
    {2, 4},
    {3, 5}
  ]

/-- The exact 11-message multiple-unicast instance studied by Sun and Jafar. -/
@[capacity_problem "sun-jafar-11-message-index-coding", capacity_definition]
def sunJafar11 : Instance 11 where
  interference := sunJafar11Interference
  self_not_interference receiver := by
    fin_cases receiver <;> simp [sunJafar11Interference]

end CapacityAtlas.IndexCoding
