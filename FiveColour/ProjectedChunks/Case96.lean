module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case96
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316067356670242690991128995089241381324883159629268587142606678188643007664525269633977270848996193569044898350253411551006041460762889123719682258705860448461744053776547840⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨32908392998381807266727, 5789234131004114107589341883129531770018971867894994468411955019690277647892205722075211275674106338014975439019483756253420741072264203023107057131493169720857857442647115338457697929885457547814468017319544473459879838721, 0⟩]
  else (cuts[r.val-3]!).toList

theorem families_valid : ∀ r, ∀ c ∈ families r, c.Valid := by
  intro r c hc
  unfold families at hc
  split at hc
  · have he := List.mem_singleton.mp hc
    subst c
    apply cut_valid_of_weight
    decide +kernel
  · split at hc
    · have he := List.mem_singleton.mp hc
      subst c
      apply cut_valid_of_weight
      decide +kernel
    · split at hc
      · have he := List.mem_singleton.mp hc
        subst c
        apply cut_valid_of_weight
        decide +kernel
      · exact cuts_valid ⟨r.val-3, by omega⟩ c hc

namespace Part0
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316067356670242690991128995089241381324883154078513828404647242504498872532684271444344153031593134594791890850680239822887208618666203342962349541441892145298661362867634176⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 49 1 (.split 50 1 (.split 51 1 (.split 54 1 (.split 59 1 (.split 67 1 (.split 72 1 (.step 7 (.step 9 (.step 3 (.close 17)))) (.step 29 (.step 3 (.step 9 (.step 18 (.close 15)))))) (.step 3 (.close 7))) (.step 26 (.split 67 1 (.split 4 0 (.step 62 (.step 3 (.close 7))) (.step 3 (.step 18 (.step 3 (.close 9))))) (.step 3 (.close 7))))) (.step 3 (.step 9 (.step 3 (.step 57 (.step 18 (.close 26))))))) (.step 3 (.step 57 (.step 3 (.step 7 (.step 26 (.step 44 (.close 54)))))))) (.step 53 (.step 57 (.split 72 1 (.split 51 1 (.split 54 1 (.split 67 1 (.split 4 0 (.split 12 0 (.step 18 (.step 3 (.step 9 (.close 21)))) (.step 9 (.step 3 (.step 15 (.step 18 (.close 21)))))) (.step 3 (.step 18 (.step 3 (.close 9))))) (.step 3 (.close 7))) (.step 3 (.step 9 (.step 21 (.step 3 (.step 18 (.step 15 (.close 26)))))))) (.step 3 (.step 7 (.step 53 (.close 7))))) (.step 3 (.step 9 (.step 21 (.step 26 (.step 3 (.step 29 (.step 3 (.step 15 (.step 3 (.close 17)))))))))))))) (.step 52 (.step 57 (.split 72 1 (.split 51 1 (.split 54 1 (.split 67 1 (.split 4 0 (.split 12 0 (.step 18 (.step 3 (.step 9 (.close 21)))) (.step 9 (.step 3 (.step 15 (.step 18 (.close 21)))))) (.step 3 (.step 18 (.step 3 (.close 9))))) (.step 3 (.close 7))) (.step 3 (.step 9 (.step 57 (.close 3))))) (.step 3 (.step 7 (.step 52 (.close 7))))) (.step 3 (.step 9 (.step 26 (.step 29 (.step 18 (.step 40 (.step 52 (.close 3)))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316067356670242690991128995089241381324883159629268587142606678188643003185035785274294777781438954912763853238605763979608374364358157459145047206239319310890554029481394176⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 35 1 (.split 36 1 (.split 42 1 (.split 43 1 (.reuse 0) (.run (.step 3 (.step 9 (.step 3 (.step 46 (.step 52 (.step 7 (.step 9 (.step 27 (.close 46))))))))))) (.run (.step 7 (.step 31 (.step 75 (.split 49 1 (.split 50 1 (.split 54 1 (.step 31 (.step 3 (.close 7))) (.step 9 (.step 26 (.step 29 (.step 3 (.step 15 (.close 31))))))) (.step 9 (.step 18 (.step 21 (.step 26 (.step 29 (.step 31 (.close 53)))))))) (.step 9 (.step 18 (.step 26 (.step 31 (.close 52))))))))))) (.run (.step 7 (.step 31 (.step 57 (.step 75 (.split 42 1 (.split 49 1 (.split 50 1 (.step 31 (.step 3 (.close 7))) (.step 9 (.step 18 (.step 21 (.step 29 (.step 31 (.close 53))))))) (.step 9 (.step 18 (.step 31 (.close 52))))) (.step 31 (.step 7 (.step 26 (.close 29))))))))))) (.run (.step 3 (.step 9 (.step 21 (.step 38 (.step 57 (.split 36 1 (.split 42 1 (.split 49 1 (.split 59 1 (.split 51 1 (.step 75 (.step 3 (.step 29 (.split 54 1 (.step 3 (.step 9 (.step 18 (.close 15)))) (.step 9 (.step 3 (.step 18 (.step 15 (.close 21))))))))) (.step 3 (.close 9))) (.step 3 (.step 9 (.step 21 (.step 26 (.step 29 (.step 3 (.step 18 (.step 15 (.close 31)))))))))) (.step 3 (.step 9 (.step 21 (.step 29 (.step 40 (.step 52 (.step 38 (.step 57 (.step 3 (.close 15))))))))))) (.step 3 (.step 29 (.step 31 (.close 3))))) (.step 3 (.step 29 (.step 31 (.step 3 (.step 26 (.close 38))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part0.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part1

namespace Part2
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316067356670242690991128995089241381324883159629268587142606678188643007664525269633977270848996193569044898346962402436360633298096422404964205167962288132432027343162179584⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 22 1 (.split 26 1 (.split 30 1 (.split 34 1 (.reuse 0) (.run (.step 7 (.step 31 (.step 38 (.step 75 (.split 36 1 (.split 42 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 31 (.step 3 (.close 7))) (.step 9 (.step 15 (.step 29 (.close 31))))) (.step 9 (.step 15 (.step 18 (.step 21 (.step 29 (.step 31 (.close 52)))))))) (.step 9 (.step 15 (.step 18 (.step 31 (.close 52)))))) (.step 31 (.step 7 (.step 26 (.step 29 (.step 3 (.close 37))))))) (.step 31 (.close 37))))))))) (.run (.step 3 (.step 7 (.split 35 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 3 (.close 7)) (.step 3 (.close 9))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 9 (.step 29 (.close 31))))))))) (.run (.step 3 (.step 9 (.step 29 (.step 57 (.step 3 (.split 49 1 (.split 50 1 (.step 29 (.step 9 (.step 3 (.step 17 (.close 18))))) (.step 9 (.step 21 (.step 27 (.step 29 (.step 26 (.step 29 (.step 3 (.step 29 (.close 53)))))))))) (.step 9 (.step 27 (.step 52 (.step 29 (.close 3))))))))))))) (.run (.step 7 (.step 18 (.step 26 (.split 26 1 (.split 35 1 (.step 18 (.split 49 1 (.split 50 1 (.step 7 (.step 9 (.close 17))) (.step 18 (.close 9))) (.step 18 (.step 9 (.close 26))))) (.step 3 (.step 18 (.close 9)))) (.step 3 (.step 18 (.step 9 (.close 26))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part1.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part2

namespace Part3
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316067356670242690991128995089241381324883159629268587142606678188643007664525269633977270848996193569044898350253411551006041460762889121061223731834828243889481731572498432⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 21 1 (.reuse 0) (.run (.step 3 (.step 18 (.step 29 (.step 31 (.step 9 (.step 57 (.split 35 1 (.split 49 1 (.split 50 1 (.step 31 (.step 18 (.close 3))) (.step 3 (.step 18 (.close 34)))) (.step 3 (.step 18 (.step 34 (.close 52))))) (.step 18 (.step 29 (.step 15 (.step 26 (.step 15 (.close 24))))))))))))))) (.run (.step 7 (.step 18 (.step 22 (.split 22 1 (.step 22 (.split 26 1 (.split 35 1 (.step 18 (.split 49 1 (.split 50 1 (.step 7 (.step 9 (.close 17))) (.step 18 (.close 9))) (.step 18 (.step 9 (.close 22))))) (.step 3 (.step 18 (.close 9)))) (.step 3 (.step 18 (.step 9 (.close 22)))))) (.step 7 (.step 11 (.close 18))))))))) (.run (.step 7 (.step 18 (.step 21 (.split 17 1 (.split 22 1 (.step 21 (.split 26 1 (.split 35 1 (.step 18 (.split 49 1 (.split 50 1 (.step 7 (.step 9 (.close 17))) (.step 18 (.close 9))) (.step 18 (.step 9 (.close 21))))) (.step 3 (.step 18 (.close 9)))) (.step 3 (.step 18 (.step 9 (.close 21)))))) (.step 7 (.step 11 (.close 18)))) (.step 7 (.step 11 (.close 18)))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part2.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part3

namespace Part4
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316067356670242690991128995089241381324883159629268587142606678188643007664525269633977270848996193569044898350253411551006041460762889123719682258705860448461741854753292288⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 6 1 (.split 10 1 (.split 12 1 (.reuse 0) (.run (.step 3 (.step 18 (.step 9 (.step 15 (.step 29 (.step 31 (.split 21 1 (.split 35 1 (.split 49 1 (.split 50 1 (.split 59 1 (.step 31 (.step 21 (.step 9 (.step 15 (.step 22 (.step 26 (.split 72 1 (.step 3 (.step 15 (.step 3 (.close 15)))) (.step 15 (.close 3))))))))) (.step 3 (.step 9 (.step 15 (.step 3 (.step 17 (.close 18))))))) (.step 3 (.step 9 (.step 15 (.step 3 (.step 17 (.close 18))))))) (.step 3 (.step 9 (.step 15 (.step 18 (.step 21 (.step 22 (.step 26 (.step 3 (.step 34 (.close 52))))))))))) (.step 9 (.step 15 (.step 21 (.step 22 (.step 26 (.step 29 (.step 3 (.step 22 (.close 26)))))))))) (.step 3 (.step 9 (.step 15 (.step 3 (.step 18 (.close 15))))))))))))))) (.run (.step 3 (.step 7 (.step 15 (.split 26 1 (.split 35 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 3 (.close 7)) (.step 3 (.step 9 (.close 15)))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 9 (.step 15 (.close 29))))) (.step 3 (.step 15 (.close 29))))))))) (.run (.step 3 (.step 9 (.step 11 (.step 9 (.step 3 (.step 18 (.step 9 (.step 3 (.step 15 (.step 22 (.step 26 (.close 31))))))))))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part3.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part4

namespace Part5
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316067356670242690991128995089241381324883159629268587142606678188643007664525269633977270848996193569044898350253411551006041460762889123719682258705860448461744053776547840⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 4 1 (.reuse 0) (.run (.step 3 (.step 7 (.split 6 1 (.step 7 (.split 12 1 (.split 26 1 (.split 35 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 3 (.close 7)) (.step 3 (.close 9))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 9 (.step 29 (.close 31))))) (.step 3 (.close 29))) (.step 3 (.step 9 (.step 15 (.close 29)))))) (.step 3 (.close 9)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  fin_cases i
  · exact Part4.excludes

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part5

/-- All chunk exclusions compose to the original concrete root. -/
theorem excludes : Chunks.Excludes 15 families root := Part5.excludes
end FiveColour.Packed.ProjectedChunks.Case96
