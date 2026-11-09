module
public import FiveColour.ClassificationProjection
public import FiveColour.EnumerationChunks.Case140
public import FiveColour.EnumerationChunks.Case141
public import FiveColour.EnumerationChunks.Case142
public import FiveColour.EnumerationChunks.Case143
public import FiveColour.EnumerationChunks.Case144
public import FiveColour.EnumerationChunks.Case145
public import FiveColour.EnumerationChunks.Case146
public import FiveColour.EnumerationChunks.Case147
public import FiveColour.EnumerationChunks.Case148
public import FiveColour.EnumerationChunks.Case149
public import FiveColour.EnumerationChunks.Case150
public import FiveColour.EnumerationChunks.Case151
public import FiveColour.EnumerationChunks.Case152
public import FiveColour.EnumerationChunks.Case153
public import FiveColour.EnumerationChunks.Case154
public import FiveColour.EnumerationChunks.Case155
public import FiveColour.EnumerationChunks.Case156
public import FiveColour.EnumerationChunks.Case157
public import FiveColour.EnumerationChunks.Case158
public import FiveColour.EnumerationChunks.Case159
@[expose] public section
namespace FiveColour.Packed.EnumerationChunks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def group7Roots : Fin 20 → Fin 357 := ![27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46]
def group7Points : Fin 20 → List Nat := ![[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
theorem group7Covered : ∀ i, Enumeration.Covers (group7Points i) 14 (Enumeration.families (group7Roots i)) (Archive.root (group7Roots i)) := by
  intro i
  fin_cases i
  · exact ClassificationProjected.covered 139 Case140.excludes
  · exact ClassificationProjected.covered 140 Case141.excludes
  · exact ClassificationProjected.covered 141 Case142.excludes
  · exact ClassificationProjected.covered 142 Case143.excludes
  · exact ClassificationProjected.covered 143 Case144.excludes
  · exact ClassificationProjected.covered 144 Case145.excludes
  · exact ClassificationProjected.covered 145 Case146.excludes
  · exact ClassificationProjected.covered 146 Case147.excludes
  · exact ClassificationProjected.covered 147 Case148.excludes
  · exact ClassificationProjected.covered 148 Case149.excludes
  · exact ClassificationProjected.covered 149 Case150.excludes
  · exact ClassificationProjected.covered 150 Case151.excludes
  · exact ClassificationProjected.covered 151 Case152.excludes
  · exact ClassificationProjected.covered 152 Case153.excludes
  · exact ClassificationProjected.covered 153 Case154.excludes
  · exact ClassificationProjected.covered 154 Case155.excludes
  · exact ClassificationProjected.covered 155 Case156.excludes
  · exact ClassificationProjected.covered 156 Case157.excludes
  · exact ClassificationProjected.covered 157 Case158.excludes
  · exact ClassificationProjected.covered 158 Case159.excludes
end FiveColour.Packed.EnumerationChunks
