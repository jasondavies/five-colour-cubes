module
public import FiveColour.PackedCalibration
public import FiveColour.PackedChunks
@[expose] public section
namespace FiveColour.Packed.ProjectedChunks.Case94
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316078689614047697084545150148163782620624926751097474402689512192122463752716786658800896252834569165382905558274374120494988700145569283070011033638732573267985122734374912⟩
def families (r : Fin 78) : List Cut :=
  if r.val = 0 then [⟨0, 0, 0⟩]
  else if r.val = 1 then [⟨37778931862957161709567, 5789234136395753411692881238169227500374407193496930116368373143805044077937094972115936759690115912617314174413936735084852813557058259367152415505988832845545998909917068502141873407714778287950081323505138605108075955201, 15⟩]
  else if r.val = 2 then [⟨32908284911715872467959, 5789234131009374248507346766749891415336450807595823763245543538954566673098291978060620411604367456060410719691003773395856797335276228224145743890145446228163347693427359436041631246125966867020082117046907873927859536897, 0⟩]
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
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316078689614047697084538596973606959289732804951437933850016123799982697003534370046865614903351744771731333331296157973354766434133636294203469408702357695987131847226163200⟩
def references : Fin 0 → Box := Fin.elim0
def proof : Chunks.Proof 0 := (.run (.split 51 1 (.split 54 1 (.step 58 (.split 56 1 (.split 59 1 (.split 67 1 (.step 75 (.split 55 1 (.split 72 1 (.step 7 (.step 18 (.step 3 (.step 28 (.step 12 (.step 15 (.close 16))))))) (.step 29 (.step 3 (.step 18 (.step 26 (.close 12)))))) (.step 18 (.step 31 (.step 3 (.step 9 (.step 18 (.step 12 (.close 21))))))))) (.step 3 (.close 7))) (.step 26 (.split 67 1 (.step 31 (.close 62)) (.step 3 (.close 7))))) (.step 3 (.step 58 (.step 75 (.split 59 1 (.split 72 1 (.split 10 0 (.split 12 0 (.split 21 0 (.split 49 0 (.step 28 (.step 3 (.step 21 (.close 22)))) (.step 3 (.step 22 (.step 16 (.step 21 (.close 26)))))) (.step 3 (.close 22))) (.step 10 (.step 22 (.step 28 (.step 3 (.step 12 (.step 15 (.close 21)))))))) (.step 3 (.step 12 (.close 15)))) (.step 28 (.step 31 (.close 3)))) (.step 3 (.step 22 (.step 26 (.step 28 (.step 31 (.close 12)))))))))))) (.step 3 (.step 9 (.step 57 (.step 58 (.step 75 (.step 58 (.split 56 1 (.step 57 (.step 62 (.step 18 (.step 16 (.close 26))))) (.step 22 (.step 31 (.step 3 (.close 21)))))))))))) (.step 3 (.step 7 (.step 26 (.step 44 (.close 54)))))))
theorem accepted : Chunks.check 15 families references root proof = true := by decide +kernel

theorem root_valid : root.Valid := by decide +kernel

theorem references_excluded : ∀ i, Chunks.Excludes 15 families (references i) := by
  intro i
  exact Fin.elim0 i

theorem excludes : Chunks.Excludes 15 families root :=
  Chunks.check_sound 15 families families_valid references references_excluded proof root root_valid accepted
end Part0

namespace Part1
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316078689614047697084545150148163782620624926745682103906354870414032147597141660462029411235339025564680251107110324466951871222776258559265407727875325580762790469511938048⟩
def references : Fin 1 → Box := ![Part0.root]
def proof : Chunks.Proof 1 := (.split 43 1 (.split 49 1 (.split 50 1 (.reuse 0) (.run (.step 57 (.step 58 (.step 53 (.split 51 1 (.split 67 1 (.split 72 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.step 18 (.step 9 (.step 21 (.step 3 (.step 29 (.step 12 (.step 15 (.close 16)))))))) (.step 53 (.close 3))) (.step 3 (.step 21 (.step 22 (.close 31))))) (.step 48 (.step 31 (.step 9 (.step 21 (.close 53)))))) (.step 9 (.step 21 (.step 53 (.step 31 (.step 53 (.close 3))))))) (.step 9 (.step 21 (.step 26 (.step 29 (.step 18 (.step 31 (.step 3 (.close 12))))))))) (.step 3 (.step 7 (.step 9 (.step 27 (.step 52 (.close 53))))))) (.step 3 (.step 7 (.step 53 (.close 7)))))))))) (.run (.step 57 (.step 58 (.step 52 (.split 51 1 (.split 67 1 (.split 72 1 (.split 50 1 (.split 54 1 (.split 55 1 (.split 56 1 (.split 59 1 (.step 18 (.step 9 (.step 31 (.close 52)))) (.step 52 (.close 3))) (.step 3 (.step 16 (.step 22 (.close 31))))) (.step 48 (.step 31 (.step 9 (.close 52))))) (.step 9 (.step 52 (.step 57 (.close 3))))) (.step 52 (.step 3 (.close 21)))) (.step 9 (.step 26 (.step 29 (.step 31 (.step 40 (.step 52 (.step 31 (.step 52 (.step 57 (.step 18 (.step 12 (.close 16))))))))))))) (.step 3 (.step 7 (.step 26 (.step 44 (.close 52)))))) (.step 3 (.step 52 (.close 7))))))))) (.run (.step 3 (.step 46 (.step 9 (.step 27 (.step 46 (.close 52))))))))
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
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316078689614047697084545150148163782620624926751097474402689512192117872275995322156095181543486726335220267316648389986849846426062063772743199011556051400896420055303061504⟩
def references : Fin 1 → Box := ![Part1.root]
def proof : Chunks.Proof 1 := (.split 36 1 (.split 38 1 (.split 42 1 (.reuse 0) (.run (.step 7 (.step 31 (.step 75 (.split 49 1 (.split 50 1 (.step 31 (.step 7 (.step 28 (.step 3 (.step 26 (.close 45)))))) (.step 9 (.step 18 (.step 21 (.step 26 (.step 29 (.step 31 (.close 53)))))))) (.step 9 (.step 18 (.step 26 (.step 31 (.close 52))))))))))) (.run (.step 3 (.step 21 (.step 58 (.split 42 1 (.split 49 1 (.split 54 1 (.split 59 1 (.step 41 (.step 58 (.step 75 (.split 72 1 (.split 10 0 (.split 12 0 (.split 16 0 (.step 28 (.step 41 (.step 3 (.step 21 (.step 16 (.close 22)))))) (.step 3 (.step 21 (.close 28)))) (.step 10 (.step 21 (.step 28 (.step 31 (.close 3)))))) (.step 3 (.step 12 (.step 15 (.step 22 (.close 28)))))) (.step 28 (.step 31 (.step 3 (.step 22 (.close 38))))))))) (.step 3 (.step 21 (.step 26 (.step 28 (.step 31 (.step 12 (.close 41)))))))) (.step 10 (.step 21 (.step 31 (.step 3 (.step 41 (.close 57))))))) (.step 3 (.step 16 (.step 21 (.step 31 (.step 41 (.step 52 (.step 41 (.close 58))))))))) (.step 31 (.step 28 (.step 41 (.close 3)))))))))) (.run (.step 7 (.step 31 (.step 57 (.step 75 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.step 31 (.step 7 (.step 22 (.step 28 (.step 3 (.step 22 (.close 39))))))) (.step 9 (.step 18 (.step 21 (.step 22 (.step 29 (.step 31 (.close 53)))))))) (.step 9 (.step 18 (.step 22 (.step 31 (.close 52)))))) (.step 31 (.close 39))) (.step 21 (.step 31 (.step 28 (.close 39)))))))))))
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
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316078689614047697084545150148163782620624926751097474402689512192122463752716786658800896252830863818527308066736477340499328191050912047351399240202844799284300262257197056⟩
def references : Fin 1 → Box := ![Part2.root]
def proof : Chunks.Proof 1 := (.split 30 1 (.split 34 1 (.split 35 1 (.reuse 0) (.run (.step 3 (.step 9 (.step 21 (.step 38 (.step 57 (.step 3 (.step 75 (.step 58 (.split 36 1 (.split 38 1 (.split 49 1 (.step 29 (.split 42 1 (.split 56 1 (.split 59 1 (.step 38 (.step 3 (.step 18 (.step 12 (.step 15 (.close 16)))))) (.step 21 (.step 26 (.step 18 (.step 31 (.close 12)))))) (.step 31 (.step 3 (.step 22 (.close 38))))) (.step 31 (.step 3 (.step 38 (.close 3)))))) (.step 9 (.step 21 (.step 29 (.step 31 (.step 40 (.step 52 (.step 57 (.step 31 (.step 26 (.step 18 (.step 31 (.close 12))))))))))))) (.step 29 (.step 31 (.close 38)))) (.step 29 (.step 31 (.step 38 (.step 3 (.step 22 (.close 39))))))))))))))))) (.run (.step 7 (.step 31 (.step 38 (.step 75 (.split 36 1 (.split 38 1 (.split 42 1 (.split 49 1 (.split 50 1 (.step 31 (.close 37)) (.step 9 (.step 15 (.step 18 (.step 21 (.step 29 (.step 31 (.close 52)))))))) (.step 9 (.step 15 (.step 16 (.step 18 (.step 31 (.close 52))))))) (.step 31 (.close 37))) (.step 16 (.step 21 (.step 28 (.step 31 (.close 37)))))) (.step 31 (.close 37))))))))) (.run (.step 3 (.step 7 (.split 35 1 (.step 3 (.step 7 (.close 18))) (.step 3 (.step 29 (.close 31))))))))
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
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316078689614047697084545150148163782620624926751097474402689512192122463752716786658800896252834569165382905558274374120494988700145569280411552506767700371001568008767275008⟩
def references : Fin 1 → Box := ![Part3.root]
def proof : Chunks.Proof 1 := (.split 16 1 (.split 17 1 (.split 21 1 (.split 22 1 (.split 26 1 (.reuse 0) (.run (.step 3 (.step 9 (.step 29 (.step 3 (.step 57 (.step 58 (.split 38 1 (.step 29 (.split 49 1 (.split 54 1 (.split 55 1 (.split 50 1 (.step 29 (.step 3 (.step 17 (.close 18)))) (.step 9 (.step 21 (.step 27 (.step 29 (.step 26 (.step 29 (.step 3 (.close 53))))))))) (.step 18 (.close 29))) (.step 9 (.step 29 (.step 3 (.step 26 (.step 27 (.close 53))))))) (.step 9 (.step 27 (.step 52 (.step 57 (.step 29 (.step 21 (.step 26 (.step 29 (.step 3 (.step 18 (.close 52))))))))))))) (.step 21 (.step 28 (.close 29)))))))))))) (.run (.step 7 (.step 18 (.step 3 (.step 18 (.step 26 (.step 18 (.close 7))))))))) (.run (.step 3 (.step 18 (.step 31 (.step 58 (.split 26 1 (.split 35 1 (.split 38 1 (.step 57 (.step 18 (.step 48 (.step 57 (.step 3 (.step 4 (.step 48 (.split 49 1 (.split 50 1 (.step 18 (.step 15 (.close 24))) (.step 3 (.step 18 (.close 34)))) (.step 3 (.step 18 (.step 34 (.close 52)))))))))))) (.step 3 (.step 4 (.step 5 (.step 21 (.step 4 (.step 22 (.step 3 (.close 4))))))))) (.step 4 (.step 9 (.step 18 (.step 29 (.step 31 (.close 38))))))) (.step 4 (.step 9 (.step 18 (.close 29))))))))))) (.run (.step 7 (.step 18 (.step 22 (.step 18 (.split 22 1 (.step 22 (.step 18 (.close 7))) (.step 7 (.close 18))))))))) (.run (.step 7 (.step 18 (.step 21 (.step 18 (.split 17 1 (.step 21 (.split 22 1 (.step 21 (.step 18 (.close 7))) (.step 7 (.close 18)))) (.step 7 (.close 18)))))))))
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
def root : Box := ⟨3221225472, 16546956789305976592836116594320052230387700316078689614047697084545150148163782620624926751097474402689512192122463752716786658800896252834569165382905558274374120494988700145569283070011033638732573267985122734374912⟩
def references : Fin 1 → Box := ![Part4.root]
def proof : Chunks.Proof 1 := (.split 10 1 (.split 12 1 (.reuse 0) (.run (.step 3 (.step 18 (.step 9 (.step 15 (.step 21 (.step 22 (.step 26 (.step 29 (.step 31 (.step 57 (.split 21 1 (.split 35 1 (.split 38 1 (.step 9 (.split 49 1 (.split 50 1 (.step 31 (.split 55 1 (.split 56 1 (.step 15 (.step 3 (.step 75 (.split 59 1 (.step 3 (.step 15 (.close 3))) (.step 15 (.close 3)))))) (.step 3 (.step 15 (.step 16 (.step 22 (.step 15 (.step 3 (.step 15 (.step 26 (.step 3 (.close 28))))))))))) (.step 3 (.step 12 (.step 29 (.step 48 (.step 15 (.step 31 (.step 15 (.step 28 (.close 31))))))))))) (.step 3 (.step 15 (.step 18 (.step 21 (.step 3 (.step 12 (.step 3 (.step 26 (.step 3 (.step 32 (.step 48 (.close 53))))))))))))) (.step 3 (.step 12 (.step 15 (.step 3 (.step 21 (.step 3 (.step 26 (.step 3 (.step 34 (.close 52)))))))))))) (.step 3 (.step 10 (.step 12 (.step 15 (.step 16 (.step 21 (.step 29 (.step 31 (.step 3 (.step 15 (.close 41)))))))))))) (.step 9 (.step 15 (.step 21 (.step 29 (.step 3 (.step 31 (.step 4 (.close 18))))))))) (.step 3 (.step 4 (.step 9 (.step 15 (.close 3)))))))))))))))))) (.run (.step 3 (.step 7 (.step 15 (.split 26 1 (.split 35 1 (.split 49 1 (.split 50 1 (.split 54 1 (.step 3 (.close 7)) (.step 3 (.close 15))) (.step 3 (.close 7))) (.step 3 (.step 7 (.close 18)))) (.step 3 (.step 15 (.close 29)))) (.step 3 (.step 15 (.close 29)))))))))
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
end FiveColour.Packed.ProjectedChunks.Case94
