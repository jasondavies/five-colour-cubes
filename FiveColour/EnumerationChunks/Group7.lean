module
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
def group7Roots : Fin 20 → Fin 357 := ![27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46]
def group7Points : Fin 20 → List Nat := ![Case140.points,Case141.points,Case142.points,Case143.points,Case144.points,Case145.points,Case146.points,Case147.points,Case148.points,Case149.points,Case150.points,Case151.points,Case152.points,Case153.points,Case154.points,Case155.points,Case156.points,Case157.points,Case158.points,Case159.points]
theorem group7Covered : ∀ i, Enumeration.Covers (group7Points i) 14 (Enumeration.families (group7Roots i)) (Archive.root (group7Roots i)) := by
  intro i
  fin_cases i
  · exact Case140.covered
  · exact Case141.covered
  · exact Case142.covered
  · exact Case143.covered
  · exact Case144.covered
  · exact Case145.covered
  · exact Case146.covered
  · exact Case147.covered
  · exact Case148.covered
  · exact Case149.covered
  · exact Case150.covered
  · exact Case151.covered
  · exact Case152.covered
  · exact Case153.covered
  · exact Case154.covered
  · exact Case155.covered
  · exact Case156.covered
  · exact Case157.covered
  · exact Case158.covered
  · exact Case159.covered
end FiveColour.Packed.EnumerationChunks
